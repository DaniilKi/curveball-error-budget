"""Failure controls for the bounded compiler wrapper; no Lean or RNG execution."""
from pathlib import Path
import json,subprocess,sys,tempfile,time,unittest
from unittest.mock import patch
import build

class Child:
    def __init__(self):self.pid=123;self.terminated=False;self.killed=False
    def poll(self):return 0 if self.terminated else None
    def kill(self):self.killed=True;self.terminated=True
    def wait(self,timeout=None):self.terminated=True;return 0

class Guards(unittest.TestCase):
    def call(self,folder):
        return build.run_guarded(['fake-lean'],folder,{},Path(folder)/'module.log',time.monotonic()+30)
    def test_low_initial_memory_launches_no_child(self):
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={"physical":0,"commit":0}),patch.object(build.subprocess,'Popen') as popen:
            with self.assertRaises(RuntimeError):self.call(t)
            popen.assert_not_called();r=json.loads((Path(t)/'module.log.json').read_bytes())
            self.assertTrue(r['child_terminated']);self.assertEqual(r['status'],'failed')
    def test_unreadable_initial_memory_launches_no_child(self):
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',side_effect=OSError('unreadable')),patch.object(build.subprocess,'Popen') as popen:
            with self.assertRaises(OSError):self.call(t)
            popen.assert_not_called()
    def test_unreadable_child_memory_kills_and_reaps(self):
        child=Child()
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={"physical":8*1024**3,"commit":8*1024**3}),patch.object(build,'resident_memory',side_effect=OSError('unreadable')),patch.object(build.subprocess,'Popen',return_value=child):
            with self.assertRaises(OSError):self.call(t)
            self.assertTrue(child.killed);self.assertTrue(child.terminated)
            self.assertTrue(json.loads((Path(t)/'module.log.json').read_bytes())['child_terminated'])
    def test_resident_limit_kills_and_reaps(self):
        child=Child()
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={"physical":8*1024**3,"commit":8*1024**3}),patch.object(build,'resident_memory',return_value=2*1024**3),patch.object(build.subprocess,'Popen',return_value=child):
            with self.assertRaises(RuntimeError):self.call(t)
            self.assertTrue(child.killed)
    def test_time_limit_kills_and_reaps(self):
        child=Child()
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={"physical":8*1024**3,"commit":8*1024**3}),patch.object(build.subprocess,'Popen',return_value=child):
            with self.assertRaises(TimeoutError):build.run_guarded(['fake'],t,{},Path(t)/'module.log',time.monotonic()+30,per_module_seconds=0)
            self.assertTrue(child.killed)
    def test_compile_error_retains_log_and_failure_receipt(self):
        child=Child();child.terminated=True
        def launch(*args,**kwargs):kwargs['stdout'].write(b'error: synthetic failure\n');return child
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={"physical":8*1024**3,"commit":8*1024**3}),patch.object(build.subprocess,'Popen',side_effect=launch):
            with self.assertRaises(RuntimeError):self.call(t)
            self.assertIn(b'error:',(Path(t)/'module.log').read_bytes())
            self.assertEqual(json.loads((Path(t)/'module.log.json').read_bytes())['status'],'failed')
    def test_expired_budget_does_not_launch_finished_child(self):
        with tempfile.TemporaryDirectory() as t,patch.object(build.subprocess,'Popen') as launch:
            with self.assertRaises(TimeoutError):build.run_guarded(['fake'],t,{},Path(t)/'module.log',time.monotonic()-1)
            launch.assert_not_called()
            self.assertEqual(json.loads((Path(t)/'module.log.json').read_bytes())['status'],'failed_deadline')
    def test_cleanup_failure_retains_unknown_receipt(self):
        child=Child()
        child.kill=lambda:(_ for _ in ()).throw(OSError('kill failed'))
        child.wait=lambda timeout=None:(_ for _ in ()).throw(subprocess.TimeoutExpired('fake',timeout))
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={'physical':8*1024**3,'commit':8*1024**3}),patch.object(build,'resident_memory',side_effect=OSError('memory failed')),patch.object(build.subprocess,'Popen',return_value=child):
            with self.assertRaises(OSError):self.call(t)
            r=json.loads((Path(t)/'module.log.json').read_bytes())
            self.assertEqual(r['status'],'failed_cleanup');self.assertEqual(r['child_termination'],'unknown')
            self.assertEqual(len(r['cleanup_errors']),2)
    def test_zero_commit_is_rejected_despite_physical_headroom(self):
        with tempfile.TemporaryDirectory() as t,patch.object(build,'free_memory',return_value={'physical':8*1024**3,'commit':0}),patch.object(build.subprocess,'Popen') as launch:
            with self.assertRaises(RuntimeError):self.call(t)
            launch.assert_not_called()
    def test_finished_child_overrun_is_not_passed(self):
        for deadline,advance in ((200,201),(600,121)):
            child=Child();child.terminated=True;clock=[0.0]
            def launch(*args,**kwargs):clock[0]=advance;return child
            with self.subTest(deadline=deadline),tempfile.TemporaryDirectory() as t,patch.object(build.time,'monotonic',side_effect=lambda:clock[0]),patch.object(build,'headroom',return_value={'physical':8*1024**3,'commit':8*1024**3}),patch.object(build.subprocess,'Popen',side_effect=launch):
                with self.assertRaises(TimeoutError):build.run_guarded(['fake'],t,{},Path(t)/'module.log',deadline)
                self.assertNotEqual(json.loads((Path(t)/'module.log.json').read_bytes())['status'],'passed')

class Sources(unittest.TestCase):
    def test_extra_source_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);(p/'lean').mkdir();(p/'lean/Unexpected.lean').write_text('')
            (p/'PROVENANCE.json').write_text(json.dumps({'source_sha256':{},'build_order':[]}))
            with patch.object(build,'ROOT',p),self.assertRaises(ValueError):build.verify_sources()

class Setup(unittest.TestCase):
    def fixture(self,p):
        (p/'lean').mkdir();f=p/'lean/A.lean';f.write_text('example : True := True.intro\n')
        (p/'cache').mkdir()
        (p/'PROVENANCE.json').write_text(json.dumps({'source_sha256':{'A':build.digest(f)},'build_order':['A']}))
        return [str(p/'build.py'),'--lean-binary',sys.executable,'--dependency-dir',str(p/'cache'),'--output-dir',str(p/'run')]
    def test_version_failure_retains_setup_receipt(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);args=self.fixture(p)
            with patch.object(build,'ROOT',p),patch.object(sys,'argv',args),patch.object(build,'stable_headroom'),patch.object(build,'compiler_environment',side_effect=OSError('version failed')):
                with self.assertRaises(OSError):build.main()
            r=json.loads((p/'run/BUILD-RECEIPT.json').read_bytes())
            self.assertEqual(r['status'],'failed');self.assertEqual(r['attempts'],[])
            self.assertIn('version failed',r['error'])
    def test_source_mutation_during_replay_is_not_accepted(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);args=self.fixture(p)
            def compile_fake(command,cwd,env,log,deadline):
                (p/'lean/A.lean').write_text('changed while replaying')
                (p/'run/A.olean').write_bytes(b'fake')
            with patch.object(build,'ROOT',p),patch.object(sys,'argv',args),patch.object(build,'stable_headroom'),patch.object(build,'compiler_environment',return_value=({'LEAN_PATH':'mock','LEAN_NUM_THREADS':'1'},'mock')),patch.object(build,'cache_bindings',return_value={}),patch.object(build,'run_guarded',side_effect=compile_fake):
                with self.assertRaises(ValueError):build.main()
            r=json.loads((p/'run/BUILD-RECEIPT.json').read_bytes())
            self.assertEqual(r['status'],'failed');self.assertFalse(r['accepted_source_binding'])
    def test_final_aggregate_overrun_is_not_passed(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);args=self.fixture(p);clock=[0.0]
            def compile_fake(command,cwd,env,log,deadline):
                Path(command[-2]).write_bytes(b'fake object');clock[0]=601
            with patch.object(build,'ROOT',p),patch.object(sys,'argv',args),patch.object(build.time,'monotonic',side_effect=lambda:clock[0]),patch.object(build,'stable_headroom'),patch.object(build,'compiler_environment',return_value=({'LEAN_PATH':'mock','LEAN_NUM_THREADS':'1'},'mock')),patch.object(build,'cache_bindings',return_value={}),patch.object(build,'run_guarded',side_effect=compile_fake):
                with self.assertRaises(TimeoutError):build.main()
            r=json.loads((p/'run/BUILD-RECEIPT.json').read_bytes())
            self.assertNotEqual(r['status'],'passed_kernel_replay');self.assertFalse(r['accepted_source_binding'])
    def test_modified_source_rejected(self):
        with tempfile.TemporaryDirectory() as t:
            p=Path(t);(p/'lean').mkdir();(p/'lean/A.lean').write_text('changed')
            (p/'PROVENANCE.json').write_text(json.dumps({'source_sha256':{'A':'0'*64},'build_order':['A']}))
            with patch.object(build,'ROOT',p),self.assertRaises(ValueError):build.verify_sources()

if __name__=='__main__':unittest.main()
