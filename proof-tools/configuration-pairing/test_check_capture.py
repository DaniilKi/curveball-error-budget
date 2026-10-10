"""Failure/provenance controls with fake objects and mocked compiler; no Lean/RNG."""
from pathlib import Path
import contextlib,io,json,tempfile,unittest
from unittest.mock import patch
import build,check_capture as check

class CheckerControls(unittest.TestCase):
    def setUp(self):
        self.temp=tempfile.TemporaryDirectory();self.addCleanup(self.temp.cleanup)
        self.base=Path(self.temp.name);self.core=self.base/'core';self.core.mkdir()
        manifest=build.verify_sources();(self.core/'source-snapshots').mkdir()
        objects={}
        for name in manifest['build_order']:
            (self.core/'source-snapshots'/(name+'.lean')).write_bytes((build.ROOT/'lean'/(name+'.lean')).read_bytes())
            obj=self.core/(name+'.olean');obj.write_bytes(('mock '+name).encode());objects[name]=build.digest(obj)
        binary=self.base/'mock-compiler';binary.write_bytes(b'not executable')
        deps=self.base/'deps';deps.mkdir()
        row={'status':'passed_kernel_replay','accepted_source_binding':True,
             'source_manifest_sha256':build.digest(build.ROOT/'PROVENANCE.json'),
             'attempts':[{'status':'passed','child_terminated':True,'cleanup_errors':[]} for _ in objects],
             'object_sha256':objects,'resolved_binary':str(binary),'lean_binary_sha256':build.digest(binary),
             'resolved_dependency_dirs':[str(deps)],'trusted_direct_cache_bindings':{}}
        self.receipt=self.core/'BUILD-RECEIPT.json';self.receipt.write_text(json.dumps(row),encoding='utf-8')
        self.capture=self.base/'capture.json';self.capture.write_bytes((build.ROOT/'examples/retained_edge.json').read_bytes())
        self.output=self.base/'output'
        self.cache=patch.object(build,'cache_bindings',return_value={});self.cache.start();self.addCleanup(self.cache.stop)
    def args(self):return [str(self.capture),'--core-build',str(self.core),'--output-dir',str(self.output)]
    def fake_child(self,command,cwd,env,log,deadline):
        Path(command[command.index('-o')+1]).write_bytes(b'mock kernel object')
        Path(str(log)+'.json').write_text(json.dumps({'status':'passed','child_terminated':True,'cleanup_errors':[]}),encoding='utf-8')
    def invoke(self,child=None):
        with (patch.object(build,'stable_headroom'),patch.object(build,'compiler_environment',return_value=({'LEAN_PATH':'mock','LEAN_NUM_THREADS':'1'},'mock version')),
             patch.object(build,'run_guarded',side_effect=child or self.fake_child),contextlib.redirect_stdout(io.StringIO())):
            return check.main(self.args())
    def test_complete_mock_path_retains_non_scientific_status(self):
        self.invoke();r=json.loads((self.output/'CERTIFICATE-RECEIPT.json').read_bytes())
        self.assertEqual(r['status'],'passed_kernel_certificate');self.assertFalse(r['scientific_runtime_authorized'])
        self.assertEqual((self.output/'capture.original.json').read_bytes(),self.capture.read_bytes())
    def test_changed_core_object_refused(self):
        (self.core/'FiniteProbability.olean').write_bytes(b'changed')
        with self.assertRaises(ValueError):check.core_bindings(self.core)
    def test_changed_source_snapshot_refused(self):
        (self.core/'source-snapshots/RankCounting.lean').write_bytes(b'changed')
        with self.assertRaises(ValueError):check.core_bindings(self.core)
    def test_incomplete_or_failed_core_refused(self):
        original=json.loads(self.receipt.read_bytes())
        for change in ('failed','unknown','missing'):
            r=json.loads(json.dumps(original))
            if change=='failed':r['attempts'][0]['status']='failed'
            elif change=='unknown':r['attempts'][0]['child_terminated']=False
            else:r['object_sha256'].pop('RankCounting')
            self.receipt.write_text(json.dumps(r),encoding='utf-8')
            with self.subTest(change=change),self.assertRaises(ValueError):check.core_bindings(self.core)
    def test_original_capture_mutation_withholds(self):
        def mutate(*args):self.fake_child(*args);self.capture.write_bytes(b'changed')
        with self.assertRaises(ValueError):self.invoke(mutate)
        self.assertFalse(json.loads((self.output/'CERTIFICATE-RECEIPT.json').read_bytes())['kernel_checked'])
    def test_unknown_child_failure_retained(self):
        def fail(command,cwd,env,log,deadline):
            Path(str(log)+'.json').write_text(json.dumps({'status':'failed_cleanup','child_terminated':False,'cleanup_errors':['mock wait failure']}),encoding='utf-8')
            raise RuntimeError('mock child cleanup unknown')
        with self.assertRaises(RuntimeError):self.invoke(fail)
        r=json.loads((self.output/'CERTIFICATE-RECEIPT.json').read_bytes())
        self.assertFalse(r['kernel_checked']);self.assertFalse(r['compiler_attempt']['child_terminated'])
    def test_setup_failure_and_overwrite_preserve_evidence(self):
        self.receipt.write_bytes(b'{}')
        with self.assertRaises(ValueError):self.invoke()
        old=(self.output/'CERTIFICATE-RECEIPT.json').read_bytes()
        with self.assertRaises(FileExistsError):self.invoke()
        self.assertEqual(old,(self.output/'CERTIFICATE-RECEIPT.json').read_bytes())
        self.assertEqual(len(list(self.base.glob('output.setup-failure-*.json'))),1)
    def test_terminal_aggregate_overrun_withholds(self):
        clock=[0.0]
        def overrun(*args):self.fake_child(*args);clock[0]=181.0
        with patch.object(check.time,'monotonic',side_effect=lambda:clock[0]),self.assertRaises(TimeoutError):self.invoke(overrun)
        r=json.loads((self.output/'CERTIFICATE-RECEIPT.json').read_bytes())
        self.assertEqual(r['status'],'failed_deadline');self.assertFalse(r['kernel_checked'])
    def test_receipt_write_overrun_withholds(self):
        clock=[0.0];original_write=Path.write_text
        def delayed_write(path,*args,**kwargs):
            result=original_write(path,*args,**kwargs)
            if path.name=='CERTIFICATE-RECEIPT.json':clock[0]=181.0
            return result
        def near_deadline(*args):self.fake_child(*args);clock[0]=179.0
        with patch.object(check.time,'monotonic',side_effect=lambda:clock[0]),patch.object(Path,'write_text',delayed_write),self.assertRaises(TimeoutError):self.invoke(near_deadline)
        r=json.loads((self.output/'CERTIFICATE-RECEIPT.json').read_bytes())
        self.assertEqual(r['status'],'failed_deadline');self.assertFalse(r['kernel_checked']);self.assertEqual(r['wall_seconds'],181.0)

if __name__=='__main__':unittest.main(verbosity=2)
