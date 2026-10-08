"""Source-only sampling launcher: never escalates arithmetic to scientific assurance."""
from pathlib import Path
import ctypes,hashlib,json,math,os,subprocess,tempfile,time
from .arithmetic_invocation import InvocationError,sha256,verify_artifacts
from .sampling_protocol import parse_request,parse_response,reservations,MAX_REQUEST,MAX_ENTROPY,MAX_RESPONSE

class _Memory(ctypes.Structure):
 _fields_=[('length',ctypes.c_ulong),('load',ctypes.c_ulong)]+[(k,ctypes.c_ulonglong) for k in
  ['total_phys','available_phys','total_commit','available_commit','total_virtual','available_virtual','available_extended']]

def available_memory():
 if os.name!='nt':raise InvocationError('unsupported_runtime_platform')
 m=_Memory();m.length=ctypes.sizeof(m)
 if not ctypes.windll.kernel32.GlobalMemoryStatusEx(ctypes.byref(m)):raise InvocationError('memory_query_failure')
 return {'physical':m.available_phys,'commit':m.available_commit}

def memory_ok(mem):return mem['physical']>=512*2**20 and mem['commit']>=2**30

def stop_owned(process):
 """Terminate only our child; retain all bounded cleanup failures in the receipt."""
 result={'owned_process_only':True,'terminated':False,'killed':False,'errors':[]}
 try:
  if process.poll() is not None:return result
 except Exception as e:result['errors'].append('poll: '+type(e).__name__)
 try:process.terminate();result['terminated']=True
 except Exception as e:result['errors'].append('terminate: '+type(e).__name__)
 try:process.wait(timeout=2);return result
 except Exception as e:result['errors'].append('terminate wait: '+type(e).__name__)
 try:process.kill();result['killed']=True
 except Exception as e:result['errors'].append('kill: '+type(e).__name__)
 try:process.wait(timeout=2)
 except Exception as e:result['errors'].append('kill wait: '+type(e).__name__)
 return result

def read_manifest(path,expected):
 try:
  with Path(path).open('rb') as f:data=f.read(262145)
 except (OSError,TypeError,ValueError) as e:raise InvocationError('missing_installation',str(e)) from e
 if len(data)>262144 or sha256(data)!=expected:raise InvocationError('installation_digest_mismatch')
 def unique(pairs):
  d={}
  for k,v in pairs:
   if k in d:raise ValueError('duplicate key')
   d[k]=v
  return d
 try:
  m=json.loads(data,object_pairs_hook=unique)
  if not isinstance(m,dict) or type(m.get('schema')) is not int or m['schema']!=1 or m.get('protocol')!='CBSAMPLE1':raise ValueError('schema')
  if m.get('build_status')!='native_built':raise InvocationError('native_sampling_not_built')
  if any(m.get(k)is not False for k in ['scientific_guarantee_enabled','scientific_rejection_authorized','tv_assurance_authorized','ideal_randomness_claim','graph_refinement_binary_claim']):raise ValueError('installation scientific flags must be false')
  if m.get('assurance')is not None:raise ValueError('installation assurance must be null')
  if not isinstance(m['native_executable'],str) or not Path(m['native_executable']).is_absolute():raise ValueError('native path')
  artifacts=m['artifacts']
  if not isinstance(artifacts,list) or not artifacts:raise ValueError('artifacts')
  paths=[]
  for a in artifacts:
   if not isinstance(a,dict) or not isinstance(a['path'],str) or not Path(a['path']).is_absolute():raise ValueError('artifact path')
   if not isinstance(a['sha256'],str) or len(a['sha256'])!=64 or any(c not in '0123456789abcdef' for c in a['sha256']):raise ValueError('digest')
   paths.append(a['path'])
  if len({os.path.normcase(x) for x in paths})!=len(paths) or m['native_executable'] not in paths:raise ValueError('unbound executable')
  modules=m['source_modules']
  required={'NativeArithmetic','NativeGraph','NativeEntropy','NativeSubset','NativeReplay','NativeSamplingProtocol'}
  if set(modules)!=required:raise ValueError('source module set')
  if any(modules[k] not in paths or Path(modules[k]).name!=k+'.lean' for k in required):raise ValueError('unbound source')
  if m.get('accepted_core_manifest') not in paths or m.get('build_receipts') not in paths:raise ValueError('unbound provenance')
 except InvocationError:raise
 except (KeyError,ValueError,TypeError,UnicodeError) as e:raise InvocationError('invalid_installation',str(e)) from e
 verify_artifacts(m)
 contract=m.get('conditional_contract')
 if contract is not None:
  if not isinstance(contract,dict):raise InvocationError('conditional_contract_shape')
  if m.get('profile')!='optimized' or contract.get('root')!='CurveballVerified.native_prefix_request_type_I':raise InvocationError('conditional_contract_scope')
  runtime=m.get('python_runtime_sources')
  required={'arithmetic_invocation.py','sampling_invocation.py','sampling_protocol.py','sampling_cli.py','__init__.py'}
  if not isinstance(runtime,dict)or set(runtime)!=required:raise InvocationError('executing_python_binding_missing')
  for name,pin in runtime.items():
   q=Path(__file__).parent/name
   if sha256(q.read_bytes())!=pin or not any(a['path']==str(q.resolve())and a['sha256']==pin for a in artifacts):raise InvocationError('executing_python_binding_mismatch')
  expected='1af0ae50a38d8c30840528a127373b4c3824e95a7ec95bd3560ac59fc801fc48'
  if contract.get('owner_raw_proof_ledger_sha256')!=expected or contract.get('native_executable_sha256')!=next(a['sha256']for a in artifacts if a['path']==m['native_executable']):raise InvocationError('conditional_contract_binding')
  core=json.loads(Path(m['accepted_core_manifest']).read_bytes())
  if not isinstance(core,dict):raise InvocationError('conditional_proof_shape')
  if core.get('root')!=contract['root'] or core.get('owner_raw_ledger_sha256')!=expected or core.get('optimized_native_binary_sha256')!=contract['native_executable_sha256']:raise InvocationError('conditional_proof_provenance')
  bound={x['module']:x['sha256']for x in core['optimized_runtime_sources']}
  if bound!={k:next(a['sha256']for a in artifacts if a['path']==v)for k,v in modules.items()}:raise InvocationError('conditional_six_source_binding')
  if m.get('release_review_status')not in ('pending_mainreview','GO'):raise InvocationError('conditional_review_status')
  reviewpin=m.get('final_release_review_sha256')
  if m['release_review_status']=='GO'and (not isinstance(reviewpin,str)or len(reviewpin)!=64 or any(c not in '0123456789abcdef'for c in reviewpin)):raise InvocationError('conditional_review_binding')
 return m

def invoke(wire,installation,expected_sha256,*,entropy_mode='os',entropy=None,resume=False,timeout_seconds=45,evidence_dir=None,predeclared=False,fixed_degree_null=False,trust_uniform_bytes=False):
 start=time.monotonic()
 bounded_wire=isinstance(wire,bytes) and len(wire)<=MAX_REQUEST+1
 receipt={'request_sha256':sha256(wire) if bounded_wire else None,
  'request_hex':wire.hex() if bounded_wire else None,'installation_sha256':expected_sha256,
  'entropy_mode':entropy_mode,'resume':resume,'assurance':None,
  'scientific_rejection_authorized':False,'tv_assurance_authorized':False,'ideal_randomness_claim':False,
  'graph_refinement_binary_claim':False}
 try:
  # Preserve bounded malformed/preflight failures too, before any entropy exists.
  parent=Path(evidence_dir) if evidence_dir is not None else Path(tempfile.gettempdir())
  parent.mkdir(parents=True,exist_ok=True)
  run=Path(tempfile.mkdtemp(prefix='curveball-native-sampling-',dir=parent));receipt['evidence_dir']=str(run)
  if bounded_wire:(run/'request.bin').write_bytes(wire)
  if resume:raise InvocationError('resume_disabled')
  if entropy_mode not in ('os','provided'):raise InvocationError('unsupported_entropy_mode')
  if isinstance(timeout_seconds,bool) or not isinstance(timeout_seconds,(int,float)) or not math.isfinite(timeout_seconds) or not 0<timeout_seconds<=60:raise InvocationError('invalid_timeout')
  r=parse_request(wire);plan=reservations(r);receipt['reservation_plan']=plan
  manifest=read_manifest(installation,expected_sha256)
  receipt['memory_before']=available_memory()
  if not memory_ok(receipt['memory_before']):raise InvocationError('preflight_memory_guard')
  # Allocate entropy only after manifest/build preflight. One allocation, no retry.
  if entropy_mode=='os':
   if entropy is not None:raise InvocationError('ambiguous_entropy')
   tape=os.urandom(plan['entropy_bytes'])
   receipt['entropy_assumption']='OS-provided bytes are trusted; IID unbiased bits and independence from observation are unproved assumptions'
  else:
   if not isinstance(entropy,bytes) or len(entropy)!=plan['entropy_bytes']:raise InvocationError('entropy_size')
   tape=entropy
   receipt['entropy_assumption']='Deterministic supplied tape; no random-law claim'
  receipt.update({'entropy_sha256':sha256(tape),'entropy_bytes':len(tape),'entropy_allocations':1,'fresh_tape_retries':0})
  # Keep raw tape and byte logs in a private, unique run directory. Retained on failure.
  tape_path=run/'entropy.bin';tape_path.write_bytes(tape)
  out_path=run/'stdout.bin';err_path=run/'stderr.bin'
  command=[manifest['native_executable'],wire.decode('ascii'),str(tape_path)]
  receipt['command']=command
  env=os.environ.copy();env['LEAN_NUM_THREADS']='1'
  process=None
  try:
   # File-backed output avoids unbounded capture memory; regular file byte sizes
   # are monitored and only this owned process can be terminated.
   with out_path.open('wb') as out,err_path.open('wb') as err:
    process=subprocess.Popen(command,cwd=run,env=env,stdout=out,stderr=err,shell=False)
    launched=time.monotonic();stopped=None
    while process.poll() is None:
     try:process.wait(timeout=.05)
     except subprocess.TimeoutExpired:
      if not memory_ok(available_memory()):stopped='owned_process_memory_guard'
      elif out_path.stat().st_size>MAX_RESPONSE or err_path.stat().st_size>4096:stopped='output_resource_cap'
      elif time.monotonic()-launched>timeout_seconds:stopped='sampling_timeout'
      if stopped:
       receipt['owned_process_cleanup']=stop_owned(process)
       break
   with out_path.open('rb') as f:stdout=f.read(MAX_RESPONSE+1)
   with err_path.open('rb') as f:stderr=f.read(4097)
   receipt.update({'exit_code':process.returncode,'stdout_hex':stdout.hex(),'stderr_hex':stderr.hex()})
   if stopped:raise InvocationError(stopped)
  except OSError as e:raise InvocationError('sampling_launch_failure',str(e)) from e
  finally:
   if process is not None:
    cleanup=stop_owned(process)
    if cleanup['errors'] or cleanup['terminated'] or cleanup['killed']:
     receipt['owned_process_final_cleanup']=cleanup
  verify_artifacts(manifest)
  if sha256(Path(installation).read_bytes())!=expected_sha256:raise InvocationError('installation_changed')
  if sha256(tape_path.read_bytes())!=receipt['entropy_sha256']:raise InvocationError('entropy_changed')
  receipt.update(parse_response(r,stdout,stderr,process.returncode))
  receipt['status']='completed_unassured_native_sampling'
  contract=manifest.get('conditional_contract')
  declared=predeclared is True and fixed_degree_null is True and trust_uniform_bytes is True
  eligible=contract is not None and entropy_mode=='os' and declared
  receipt['conditional_model_eligibility']=eligible
  receipt['declared_model']={'predeclared':predeclared is True,'uniform_labeled_degree_conditioned_null':fixed_degree_null is True,'independent_uniform_full_bytes_trusted':trust_uniform_bytes is True}
  if eligible:
   receipt['conditional_assurance']={'root':contract['root'],'scope':contract['scope'],'trusted_correspondences':contract['external_trust'],'refusal_policy':contract['refusal_policy']}
   receipt['release_review_status']=manifest['release_review_status']
   # Publication/semantic review is separate from accepted model-root eligibility.
   if manifest['release_review_status']=='GO':
    receipt['assurance']='conditional_native_prefix_type_I'
    receipt['scientific_rejection_authorized']=receipt['rank_predicate_passed'] is True
    receipt['status']='completed_conditional_native_sampling'
   else:receipt['scientific_hold']='Main release review GO pending; no scientific rejection authorized'
 except InvocationError as e:receipt.update({'status':'blocked','error':e.code,'detail':e.detail})
 except (OSError,TypeError,ValueError,KeyError,subprocess.SubprocessError) as e:receipt.update({'status':'blocked','error':'sampling_boundary_failure','detail':type(e).__name__+': '+str(e)})
 def clear_assurance():
  receipt.update({'assurance':None,'scientific_rejection_authorized':False,'tv_assurance_authorized':False,'ideal_randomness_claim':False,'graph_refinement_binary_claim':False,'conditional_model_eligibility':False})
  receipt.pop('conditional_assurance',None)
 if receipt.get('status')=='blocked':clear_assurance()
 receipt['seconds']=time.monotonic()-start
 if 'evidence_dir' in receipt:
  try:(Path(receipt['evidence_dir'])/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
  except OSError as e:receipt.update({'status':'blocked','error':'evidence_write_failure','detail':str(e)});clear_assurance()
 return receipt
