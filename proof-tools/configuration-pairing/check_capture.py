"""Guarded kernel check of a bounded generated captured-output certificate.

Requires a successful local core replay and its trusted cached dependencies.
This checks deterministic provided data, not execution authenticity or randomness.
"""
from pathlib import Path
import argparse,hashlib,json,time
import build
import capture_to_lean as capture

ROOT=Path(__file__).resolve().parent

def core_bindings(directory):
    directory=Path(directory).resolve(strict=True)
    path=directory/'BUILD-RECEIPT.json'
    with path.open('rb') as stream:raw=stream.read(1024*1024+1)
    if len(raw)>1024*1024:raise ValueError('core receipt exceeds local input limit')
    receipt=json.loads(raw)
    manifest=build.verify_sources()
    if receipt.get('status')!='passed_kernel_replay' or receipt.get('accepted_source_binding') is not True:
        raise ValueError('successful source-bound core replay required')
    if receipt.get('source_manifest_sha256')!=build.digest(ROOT/'PROVENANCE.json'):
        raise ValueError('core source manifest differs')
    attempts=receipt.get('attempts',[])
    if len(attempts)!=len(manifest['build_order']) or any(r.get('status')!='passed' or r.get('child_terminated') is not True or r.get('cleanup_errors') for r in attempts):
        raise ValueError('core replay lacks complete terminal success')
    objects=receipt.get('object_sha256',{})
    if set(objects)!=set(manifest['build_order']):raise ValueError('incomplete core object closure')
    bindings={path:hashlib.sha256(raw).hexdigest(),ROOT/'PROVENANCE.json':build.digest(ROOT/'PROVENANCE.json')}
    for name,h in manifest['source_sha256'].items():
        bindings[ROOT/'lean'/(name+'.lean')]=h
        bindings[directory/'source-snapshots'/(name+'.lean')]=h
        bindings[directory/(name+'.olean')]=objects[name]
    binary=Path(receipt['resolved_binary']).resolve(strict=True)
    bindings[binary]=receipt['lean_binary_sha256']
    dependencies=[Path(p).resolve(strict=True) for p in receipt['resolved_dependency_dirs']]
    if not dependencies or any(not p.is_dir() for p in dependencies):raise ValueError('missing cached dependencies')
    if any((p/(n+'.olean')).exists() for p in dependencies for n in manifest['build_order']):
        raise ValueError('cached dependencies shadow authored modules')
    caches=build.cache_bindings(manifest,binary,dependencies)
    if {str(p):h for p,h in caches.items()}!=receipt['trusted_direct_cache_bindings']:
        raise ValueError('direct dependency cache changed')
    bindings.update(caches)
    for name in ('build.py','capture_to_lean.py','check_capture.py'):bindings[ROOT/name]=build.digest(ROOT/name)
    build.verify_bindings(bindings)
    return directory,binary,dependencies,bindings

def main(argv=None):
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('capture',type=Path)
    parser.add_argument('--core-build',required=True,type=Path)
    parser.add_argument('--output-dir',required=True,type=Path,help='new directory; existing evidence is never overwritten')
    args=parser.parse_args(argv)
    started=time.monotonic();deadline=started+180;created=False
    output=args.output_dir.resolve()
    receipt={'status':'failed','kernel_checked':False,'scientific_runtime_authorized':False,'sampling_performed':False,
             'claim':'Deterministic provided finite data only; no execution authentication, uniformity or IID claim.',
             'aggregate_limit_seconds':180,'per_module_limit_seconds':120,'threads':1,'cleanup_included_in_wall_accounting':True}
    try:
        if output.exists():raise FileExistsError('new output directory required')
        output.mkdir(parents=True,exist_ok=False);created=True
        core,binary,dependencies,bindings=core_bindings(args.core_build)
        original=args.capture.resolve(strict=True)
        with original.open('rb') as stream:raw=stream.read(capture.MAX_INPUT_BYTES+1)
        if len(raw)>capture.MAX_INPUT_BYTES:raise ValueError('capture exceeds byte limit')
        snapshot=output/'capture.original.json';snapshot.write_bytes(raw)
        capture_sha=hashlib.sha256(raw).hexdigest()
        bindings[original]=capture_sha;bindings[snapshot]=capture_sha
        checked=capture.load_capture(snapshot)
        receipt['input_bindings']={str(p):h for p,h in bindings.items()}
        emitted=capture.write_new_directory(output/'generated',checked)
        source=output/'generated'/emitted['lean_source_file']
        normalized=output/'generated/capture.normalized.json'
        bindings[source]=emitted['lean_sha256'];bindings[normalized]=emitted['normalized_capture_sha256']
        receipt.update(emitted)
        observations=[];receipt['headroom_observations']=observations
        build.stable_headroom(deadline,observations);build.verify_bindings(bindings)
        env,version=build.compiler_environment(binary,[core,*dependencies],output,deadline)
        receipt.update(resolved_binary=str(binary),lean_version=version,LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS=env['LEAN_NUM_THREADS'])
        command=[binary,'-j','1','-DautoImplicit=false','-DmaxRecDepth=4096','-DmaxHeartbeats=1000000','-o',output/(source.stem+'.olean'),source]
        build.run_guarded(command,source.parent,env,output/'CERTIFICATE.log',deadline)
        build.verify_bindings(bindings)
        receipt['object_sha256']=build.digest(output/(source.stem+'.olean'))
        if time.monotonic()>=deadline:raise TimeoutError('final aggregate certificate budget exceeded')
        receipt.update(status='passed_kernel_certificate',kernel_checked=True)
    except BaseException as ex:
        receipt['error']=str(ex);raise
    finally:
        row_path=output/'CERTIFICATE.log.json'
        if created and row_path.exists():receipt['compiler_attempt']=json.loads(row_path.read_bytes())
        receipt['wall_seconds']=time.monotonic()-started
        overrun=time.monotonic()>=deadline
        if overrun:receipt.update(status='failed_deadline',kernel_checked=False,error='aggregate deadline exceeded including finalization/cleanup')
        target=output/'CERTIFICATE-RECEIPT.json' if created else output.parent/(output.name+'.setup-failure-'+str(time.time_ns())+'.json')
        target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
        if time.monotonic()>=deadline:
            overrun=True
            receipt.update(status='failed_deadline',kernel_checked=False,wall_seconds=time.monotonic()-started,
                           error='aggregate deadline exceeded including receipt serialization/write')
            target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
        if overrun:raise TimeoutError(receipt['error'])
    print(json.dumps({'status':receipt['status'],'kernel_checked':receipt['kernel_checked'],'wall_seconds':receipt['wall_seconds'],'scientific_runtime_authorized':False}))

if __name__=='__main__':main()
