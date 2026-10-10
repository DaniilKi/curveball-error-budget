"""Serial kernel replay of the pinned authored source closure.

Dependencies and the Lean binary are explicit trusted inputs. This performs no
downloads, sampling, inference, or native compilation. Receipts are local only.
"""
from pathlib import Path
import argparse,ctypes,hashlib,json,os,re,shutil,subprocess,sys,time

ROOT=Path(__file__).resolve().parent

def digest(path):return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def verify_sources():
    manifest=json.loads((ROOT/'PROVENANCE.json').read_bytes())
    pins=manifest['source_sha256'];order=manifest['build_order']
    if len(order)!=len(set(order)) or set(order)!=set(pins):raise ValueError('invalid source order')
    if {p.stem for p in (ROOT/'lean').glob('*.lean')}!=set(pins):raise ValueError('unlisted source module')
    for name,h in pins.items():
        if digest(ROOT/'lean'/(name+'.lean'))!=h:raise ValueError('source digest mismatch: '+name)
    return manifest

def free_memory():
    if os.name=='nt':
        class Memory(ctypes.Structure):
            _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(k,ctypes.c_ulonglong) for k in
                ['total_phys','available_phys','total_commit','available_commit','total_virtual','available_virtual','extended']]
        m=Memory();m.length=ctypes.sizeof(m)
        if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m)):raise OSError('memory query failed')
        return {'physical':m.available_phys,'commit':m.available_commit}
    if sys.platform.startswith('linux'):
        rows=dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
        return {'physical':int(rows['MemAvailable'].split()[0])*1024,
                'commit':(int(rows['CommitLimit'].split()[0])-int(rows['Committed_AS'].split()[0]))*1024}
    raise OSError('memory guard supports Windows/Linux only; no unchecked fallback')

def headroom(start=False):
    m=free_memory()
    if m['physical']<6*1024**3 or m['commit']<(6 if start else 2)*1024**3:
        raise RuntimeError('physical/commit headroom guard')
    return m

def resident_memory(pid):
    if os.name=='nt':
        from ctypes import wintypes
        class Counters(ctypes.Structure):
            _fields_=[('cb',wintypes.DWORD),('faults',wintypes.DWORD)]+[(k,ctypes.c_size_t) for k in
                ['peak_ws','ws','peak_paged','paged','peak_nonpaged','nonpaged','pagefile','peak_pagefile','private']]
        kernel=ctypes.windll.kernel32;psapi=ctypes.windll.psapi
        kernel.OpenProcess.argtypes=[wintypes.DWORD,wintypes.BOOL,wintypes.DWORD];kernel.OpenProcess.restype=wintypes.HANDLE
        kernel.CloseHandle.argtypes=[wintypes.HANDLE]
        psapi.GetProcessMemoryInfo.argtypes=[wintypes.HANDLE,ctypes.POINTER(Counters),wintypes.DWORD]
        handle=kernel.OpenProcess(0x410,False,pid)
        if not handle:raise OSError('cannot inspect compiler process')
        try:
            c=Counters();c.cb=ctypes.sizeof(c)
            if not psapi.GetProcessMemoryInfo(handle,ctypes.byref(c),c.cb):raise OSError('compiler memory query failed')
            return max(c.ws,c.peak_ws)
        finally:kernel.CloseHandle(handle)
    rows=dict(line.split(':',1) for line in Path('/proc',str(pid),'status').read_text().splitlines() if ':' in line)
    return int(rows['VmRSS'].split()[0])*1024

def run_guarded(command,cwd,env,log,deadline,per_module_seconds=120):
    start=time.monotonic();process=None;peak=0;failure=None
    row={'command':list(map(str,command)),'status':'failed','threads':1,'cleanup_errors':[]}
    try:
        if time.monotonic()>=deadline-15:raise TimeoutError('aggregate budget exhausted before launch')
        row['initial_memory']=headroom()
        with Path(log).open('xb') as stream:
            if time.monotonic()>=deadline-15:raise TimeoutError('aggregate budget exhausted before launch')
            process=subprocess.Popen(row['command'],cwd=cwd,env=env,stdout=stream,stderr=subprocess.STDOUT,shell=False)
            while process.poll() is None:
                if time.monotonic()>=deadline-15 or time.monotonic()-start>=per_module_seconds:raise TimeoutError('compiler time budget exceeded')
                headroom()
                try:usage=resident_memory(process.pid)
                except OSError:
                    if process.poll() is not None:break
                    raise
                peak=max(peak,usage)
                if usage>1536*1024**2:raise RuntimeError('polled compiler resident memory exceeded 1.5 GiB')
                time.sleep(.2)
            row['exit_code']=process.wait()
        text=Path(log).read_text(encoding='utf-8',errors='replace')
        if row['exit_code']!=0 or 'sorryAx' in text or 'error:' in text:raise RuntimeError('kernel replay failed; log retained')
        if time.monotonic()>=deadline or time.monotonic()-start>=per_module_seconds:
            raise TimeoutError('terminal compiler time budget exceeded')
        row['status']='passed'
    except BaseException as ex:
        row['error']=str(ex);failure=ex
    finally:
        terminated=process is None
        if process is not None:
            try:terminated=process.poll() is not None
            except BaseException as ex:row['cleanup_errors'].append('poll: '+str(ex))
            if not terminated:
                try:process.kill()
                except BaseException as ex:row['cleanup_errors'].append('kill: '+str(ex))
                try:process.wait(timeout=max(.01,min(15,deadline-time.monotonic())))
                except BaseException as ex:row['cleanup_errors'].append('wait: '+str(ex))
                try:terminated=process.poll() is not None
                except BaseException as ex:row['cleanup_errors'].append('final poll: '+str(ex))
        row.update(wall_seconds=time.monotonic()-start,polled_peak_resident_bytes=peak,child_terminated=terminated,
                   child_termination='confirmed' if terminated else 'unknown',resident_limit_bytes=1536*1024**2)
        if row['cleanup_errors'] or not terminated:
            row['status']='failed_cleanup';failure=failure or RuntimeError('compiler cleanup unconfirmed')
        if time.monotonic()>=deadline or time.monotonic()-start>=per_module_seconds:
            row['status']='failed_deadline';failure=failure or TimeoutError('terminal cleanup time budget exceeded')
        Path(str(log)+'.json').write_text(json.dumps(row,indent=2)+'\n',encoding='utf-8')
    if failure is not None:raise failure
    return row

def compiler_environment(binary,dependencies,output,deadline):
    env=os.environ.copy()
    for key in ('LEAN_PATH','LEAN_SRC_PATH','PYTHONPATH','PYTHONHOME'):env.pop(key,None)
    env.update(LEAN_NUM_THREADS='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1',MKL_NUM_THREADS='1')
    env['LEAN_PATH']=os.pathsep.join(map(str,[output,*dependencies]))
    remaining=deadline-time.monotonic()-15
    if remaining<=0:raise TimeoutError('setup budget exhausted')
    p=subprocess.run([str(binary),'--version'],capture_output=True,env=env,timeout=min(15,remaining))
    (output/'VERSION.stdout.bin').write_bytes(p.stdout);(output/'VERSION.stderr.bin').write_bytes(p.stderr)
    p.check_returncode()
    version=p.stdout.decode('utf-8')
    if 'version 4.34.1,' not in version and 'version 4.34.1)' not in version:raise ValueError('Lean 4.34.1 required: '+version)
    return env,version

def frozen_sources(manifest,output):
    snapshots=output/'source-snapshots';snapshots.mkdir()
    bindings={ROOT/'PROVENANCE.json':digest(ROOT/'PROVENANCE.json')}
    for name,h in manifest['source_sha256'].items():
        source=ROOT/'lean'/(name+'.lean');raw=source.read_bytes()
        if hashlib.sha256(raw).hexdigest()!=h:raise ValueError('source changed during setup')
        copy=snapshots/source.name;copy.write_bytes(raw);bindings[source]=h;bindings[copy]=h
    return snapshots,bindings

def cache_bindings(manifest,binary,dependencies):
    bindings={}
    names={'Init'}
    for name in manifest['build_order']:
        for imports in re.findall(r'^import (.+)$',(ROOT/'lean'/(name+'.lean')).read_text(encoding='utf-8'),re.M):
            names.update(imports.split())
    for name in names-set(manifest['build_order']):
        relative=Path(*name.split('.')).with_suffix('.olean')
        candidates=[d/relative for d in [*dependencies,binary.parent.parent/'lib/lean']]
        path=next((p for p in candidates if p.exists()),None)
        if path is None:raise FileNotFoundError('cached import not found: '+name)
        bindings[path.resolve()]=digest(path)
    return bindings

def verify_bindings(bindings):
    for path,h in bindings.items():
        if digest(path)!=h:raise ValueError('run input changed: '+str(path))

def stable_headroom(deadline,observations):
    observations.append(dict(headroom(start=True),monotonic=time.monotonic()))
    stable_until=time.monotonic()+60
    while time.monotonic()<stable_until:
        if time.monotonic()>=deadline-15:raise TimeoutError('stable headroom budget exhausted')
        time.sleep(min(1,max(0,stable_until-time.monotonic())))
        observations.append(dict(headroom(start=True),monotonic=time.monotonic()))

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--verify-only',action='store_true')
    parser.add_argument('--lean-binary',type=Path)
    parser.add_argument('--dependency-dir',type=Path,action='append',default=[])
    parser.add_argument('--lake-environment',action='store_true',help='use cached search paths from an explicit lake env invocation')
    parser.add_argument('--output-dir',type=Path,default=ROOT/'build')
    args=parser.parse_args()
    if args.verify_only:
        manifest=verify_sources()
        print(json.dumps({'status':'source_hashes_verified','modules':len(manifest['build_order']),'kernel_replay':False}));return
    if not args.lean_binary:parser.error('explicit --lean-binary required; see README')
    started=time.monotonic();deadline=started+600;attempts=[];output=args.output_dir.resolve();created=False
    receipt={'status':'failed','attempts':attempts,'sampling_performed':False,'scientific_runtime_authorized':False,'accepted_source_binding':False,'cleanup_included_in_wall_accounting':True}
    try:
        output.mkdir(parents=True,exist_ok=False);created=True
        manifest=verify_sources();receipt['source_manifest_sha256']=digest(ROOT/'PROVENANCE.json')
        snapshots,bindings=frozen_sources(manifest,output)
        if bindings[ROOT/'PROVENANCE.json']!=receipt['source_manifest_sha256']:raise ValueError('manifest changed during setup')
        verify_bindings(bindings)
        observations=[];receipt['headroom_observations']=observations
        stable_headroom(deadline,observations)
        verify_bindings(bindings)
        binary_path=args.lean_binary if args.lean_binary.exists() else shutil.which(str(args.lean_binary))
        if not binary_path:raise FileNotFoundError('compiler executable not found')
        binary=Path(binary_path).resolve(strict=True);paths=args.dependency_dir
        if args.lake_environment:
            if paths:raise ValueError('choose lake environment or explicit dependency paths')
            inherited=os.environ.get('LEAN_PATH','')
            if not inherited:raise ValueError('no Lake environment search path')
            paths=[Path(p) for p in inherited.split(os.pathsep) if p and Path(p).resolve()!=(ROOT/'.lake/build/lib/lean').resolve()]
        if not paths:raise ValueError('cached --dependency-dir or --lake-environment required; see README')
        dependencies=[d.resolve(strict=True) for d in paths]
        for d in dependencies:
            if not d.is_dir():raise ValueError('dependency path is not a directory')
            if any((d/(n+'.olean')).exists() for n in manifest['build_order']):raise ValueError('dependencies must not shadow authored modules')
        receipt.update(lean_binary_sha256=digest(binary),resolved_binary=str(binary),resolved_dependency_dirs=list(map(str,dependencies)),dependencies='cached trusted direct import objects; not a transitive rebuild')
        bindings[binary]=receipt['lean_binary_sha256']
        env,version=compiler_environment(binary,dependencies,output,deadline)
        receipt.update(lean_version=version,LEAN_PATH=env['LEAN_PATH'],LEAN_NUM_THREADS=env['LEAN_NUM_THREADS'])
        caches=cache_bindings(manifest,binary,dependencies);bindings.update(caches)
        receipt['trusted_direct_cache_bindings']={str(p):h for p,h in caches.items()}
        for name in manifest['build_order']:
            verify_bindings(bindings)
            command=[binary,'-j','1','-DautoImplicit=false','-DmaxRecDepth=4096','-DmaxHeartbeats=1000000','-o',output/(name+'.olean'),snapshots/(name+'.lean')]
            log=output/(name+'.log')
            try:run_guarded(command,snapshots,env,log,deadline)
            finally:
                row_path=Path(str(log)+'.json')
                if row_path.exists():attempts.append(json.loads(row_path.read_bytes()))
            verify_bindings(bindings)
        receipt['object_sha256']={n:digest(output/(n+'.olean')) for n in manifest['build_order']}
        verify_bindings(bindings)
        if time.monotonic()>=deadline:raise TimeoutError('final aggregate time budget exceeded')
        receipt['status']='passed_kernel_replay'
        receipt['accepted_source_binding']=True
    except BaseException as ex:
        receipt['error']=str(ex);raise
    finally:
        receipt['wall_seconds']=time.monotonic()-started
        overrun=time.monotonic()>=deadline
        if overrun:
            receipt['status']='failed_deadline';receipt['accepted_source_binding']=False
            receipt['error']='aggregate deadline exceeded, including finalization/cleanup'
        target=output/'BUILD-RECEIPT.json' if created else output.parent/(output.name+'.setup-failure-'+str(time.time_ns())+'.json')
        target.write_text(json.dumps(receipt,indent=2)+'\n',encoding='utf-8')
        if overrun:raise TimeoutError(receipt['error'])
    print(json.dumps({'status':receipt['status'],'modules':len(attempts),'wall_seconds':receipt['wall_seconds'],'sampling_performed':False}))

if __name__=='__main__':main()
