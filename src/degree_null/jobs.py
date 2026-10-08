"""Atomic streamed outputs, immutable configuration and full-restart resume."""
import hashlib, importlib.metadata, json, math, os, platform, random, re, time
from datetime import datetime,timezone
from fractions import Fraction
from pathlib import Path
from . import kernel
from .inputs import _label

def utc():return datetime.now(timezone.utc).isoformat()
def digest(data):return hashlib.sha256(data).hexdigest()
def canonical(obj):return json.dumps(obj,sort_keys=True,ensure_ascii=False,separators=(',',':')).encode()
def source_hashes():
    return {p.name:digest(p.read_bytes())for p in sorted(Path(__file__).parent.glob('*.py'))}
def environment():
    versions={}
    for name in ['networkit','numpy','scipy','psutil','networkx','tabulate']:
        try:versions[name]=importlib.metadata.version(name)
        except importlib.metadata.PackageNotFoundError:versions[name]=None
    return {'python':platform.python_version(),'platform':platform.platform(),'packages':versions,'threads':1}
def _positive(value,name):
    if type(value)is not int or value<1:raise ValueError(f'{name} must be a positive integer')
def bounded_fraction(value,name):
    text=str(value)
    if len(text)>201 or not re.fullmatch(r'(?:[0-9]{1,100}(?:/[0-9]{1,100})?|[0-9]{0,100}\.[0-9]{1,100})',text):
        raise ValueError(f'{name} must be a bounded decimal or integer fraction; scientific notation is unsupported')
    return Fraction(text)
def make_plan(network,samples,joint_tv,seed=131001,backend='networkit',statistic=None,alpha='1/20'):
    _positive(samples,'samples')
    if samples>1000:raise ValueError('samples exceeds1000 prototype limit')
    if type(seed)is not int or not 0<=seed<=2**64-samples:raise ValueError('seed range must fit unsigned64-bit')
    if backend not in ['networkit','reference']:raise ValueError('unsupported backend')
    if statistic not in [None,'triangles']:raise ValueError('only predeclared triangles supported')
    level=bounded_fraction(alpha,'alpha')
    if not 0<level<1:raise ValueError('alpha must lie in(0,1)')
    total=bounded_fraction(joint_tv,'TV');kernel.parse_epsilon(total)
    if statistic and level<=total:raise ValueError('overall alpha target must exceed jointTV; choose a smallerTV budget')
    adj=kernel.validate_graph(network['graph']);degrees=[len(x)for x in adj]
    if len(network['labels'])!=len(adj)or len(set(network['labels']))!=len(adj):raise ValueError('labels must form a bijective node mapping')
    for label in network['labels']:_label(label)
    if network['degrees']!=degrees:raise ValueError('input degree metadata mismatch')
    normalized={'graph':network['graph'],'labels':network['labels']}
    if digest(canonical(normalized))!=network['normalized_input_sha256']:raise ValueError('normalized input hash mismatch')
    per=total/samples;cert=kernel.certificate(degrees,str(per));cutoff=max(Fraction(0),level-total)
    trades=cert['attempted_pair_trades']*samples;n=len(adj)
    # Explicit pilot-based planning heuristic, not a certified runtime estimate.
    rate=500000*64/max(64,n)if backend=='networkit'else 100000*64/max(64,n)
    config={'samples':samples,'joint_tv':str(total),'per_output_tv':str(per),'seed':seed,'backend':backend,'statistic_predeclared':statistic,'overall_alpha_target':str(level),'raw_rank_cutoff':str(cutoff)}
    return {'status':'planned','config':config,'certificate_plan':cert,'total_attempted_pair_trades':trades,
      'minimum_rank_score':str(Fraction(1,samples+1)),'coarse_rank_warning':bool(statistic and Fraction(1,samples+1)>cutoff),
      'rough_runtime_seconds':2+trades/rate,'runtime_estimate_scope':'rough planning only;500000 compiled or100000 reference trades/s atn<=64, scaled64/n above; hardware,density,imports affecttime; not a promise',
      'approx_graph_bytes_total':samples*(4096+200*len(adj)+40*len(network['graph']['edges'])),
      'input':network,'source_hashes':source_hashes(),'source_commit':kernel.SOURCE_COMMIT,
      'assurance':'CONDITIONAL on manuscript pair-resampling operator bound and ideal independent uniform random draws; no machineverified end-to-end theorem or finite-PRNG exactness',
      'restart_policy':'each output starts from original input; seed+index; interrupted output is discarded and fully replayed on resume',
      'joint_contract':'batchTV <=sum per-outputTV under stated theorem and independent ideal randomness assumptions',
      'model_scope':'uniform labeled simple undirected graphs with same per-label degrees; disconnected graphs included'}

def atomic(path,obj):
    path=Path(path);temporary=path.with_name(path.name+'.tmp')
    with temporary.open('wb')as handle:
        handle.write(canonical(obj)+b'\n');handle.flush();os.fsync(handle.fileno())
    os.replace(temporary,path)
def load(path):return json.loads(Path(path).read_text(encoding='utf-8'))
def folder_bytes(folder):return sum(p.stat().st_size for p in Path(folder).iterdir()if p.is_file())
def verify_stored_plan(folder,plan):
    scientific={k:plan[k]for k in ['config','input','certificate_plan','source_hashes','source_commit','environment']}
    if digest(canonical(scientific))!=plan['job_fingerprint']:raise ValueError('immutable plan fingerprint mismatch')
    if load(Path(folder)/'labels.json')!=plan['input']['labels']:raise ValueError('saved label mapping mismatch')
    return plan

class Paused(RuntimeError):pass
class Meter:
    def __init__(self,max_seconds,max_rss_mib,folder):
        import psutil
        if not math.isfinite(max_seconds)or max_seconds<=0:raise ValueError('max-seconds must be positive finite')
        if not math.isfinite(max_rss_mib)or max_rss_mib<=0:raise ValueError('max-rss must be positive finite')
        self.process=psutil.Process();self.start=time.perf_counter();self.cpu0=sum(self.process.cpu_times()[:2]);self.peak=0
        self.max_seconds=max_seconds;self.max_rss_mib=max_rss_mib;self.folder=folder
    def check(self):
        mem=self.process.memory_info();self.peak=max(self.peak,mem.rss,getattr(mem,'peak_wset',0))
        if(self.folder/'STOP').exists():raise Paused('STOP file requested cancellation; remove it before resume')
        if time.perf_counter()-self.start>self.max_seconds:raise Paused('wall-time limit reached; unfinished output discarded')
        if mem.rss>self.max_rss_mib*2**20:raise Paused('current RSS limit reached; unfinished output discarded')
    def data(self):
        return {'seconds':time.perf_counter()-self.start,'cpu_seconds':sum(self.process.cpu_times()[:2])-self.cpu0,
          'peak_process_MiB':self.peak/2**20,'peak_scope':'chunk-boundary sampled RSS plus lifetime Windowspeak_wset; lifetime peak may precede this invocation',
          'max_seconds':self.max_seconds,'max_rss_MiB':self.max_rss_mib}

def _one(spec,cert,seed,backend,meter):
    adj=kernel.validate_graph(spec);remaining=cert['attempted_pair_trades'];meter.check()
    if remaining and backend=='networkit':
        nk=kernel.get_networkit();nk.setSeed(seed,False);g=nk.Graph(len(adj),weighted=False,directed=False)
        for a,b in kernel.edges_from_adj(adj):g.addEdge(a,b)
        cb=nk.randomization.Curveball(g)
        while remaining:
            meter.check();count=min(10000,remaining)
            pairs=nk.randomization.CurveballUniformTradeGenerator(count,len(adj)).generate()
            if len(pairs)!=count:raise RuntimeError('trade generator count mismatch')
            cb.run(pairs);remaining-=count
        g=cb.getGraph();adj=[set(g.iterNeighbors(i))for i in range(len(adj))]
    elif remaining:
        rng=random.Random(seed);n=len(adj)
        for step in range(remaining):
            if step%1000==0:meter.check()
            i=rng.randrange(n);j=rng.randrange(n-1);j+=j>=i
            kernel.reference_trade(adj,i,j,rng)
    graph={'n':len(adj),'edges':kernel.edges_from_adj(adj)}
    if [len(x)for x in kernel.validate_graph(graph)]!=cert['degrees']:raise RuntimeError('degree invariant failed')
    meter.check();return graph

def _verify_outputs(folder,plan):
    paths=sorted(folder.glob('graph-*.json'));completed=[]
    for index,path in enumerate(paths):
        if path.name!=f'graph-{index:06d}.json':raise ValueError('saved output indices have a gap or extra file')
        result=load(path);graph=result['graph'];cert=plan['certificate_plan'];config=plan['config']
        if index>=config['samples']or result['index']!=index or result['seed']!=config['seed']+index:raise ValueError('saved output index/seed mismatch')
        if result['status']!='completed_conditional_certificate'or result['certificate']!=cert:raise ValueError('saved output certificate mismatch')
        if result['graph_sha256']!=digest(canonical(graph)):raise ValueError('saved graph hash mismatch')
        if [len(a)for a in kernel.validate_graph(graph)]!=cert['degrees']:raise ValueError('saved graph degree mismatch')
        if result['job_fingerprint']!=plan['job_fingerprint']:raise ValueError('saved output belongs to another job')
        completed.append(path.name)
    return completed

def _lock(folder,recover):
    import psutil
    path=folder/'RUNNING.lock'
    if path.exists():
        previous=load(path);live=False
        try:live=abs(psutil.Process(previous['pid']).create_time()-previous['process_created'])<.01
        except psutil.NoSuchProcess:pass
        if live:raise ValueError('job is active in another process')
        if not recover:raise ValueError('stale lock after interrupted process; inspect job then use --recover-stale-lock')
        path.unlink()
    handle=os.open(path,os.O_CREAT|os.O_EXCL|os.O_WRONLY)
    with os.fdopen(handle,'w')as stream:json.dump({'pid':os.getpid(),'process_created':psutil.Process().create_time(),'utc':utc()},stream)
    return path

def run_job(plan,folder,max_trades=10000000,max_seconds=60,max_rss_mib=256,max_output_mib=128,stop_after=None,recover_stale_lock=False,resume=False):
    """Stream whole outputs. Resume verifies frozen evidence and restarts unfinished output."""
    config=plan['config']
    expected=make_plan(plan['input'],config['samples'],config['joint_tv'],config['seed'],config['backend'],config['statistic_predeclared'],config['overall_alpha_target'])
    for key in ['config','certificate_plan','total_attempted_pair_trades','approx_graph_bytes_total','source_hashes','source_commit']:
        if plan[key]!=expected[key]:raise ValueError(f'plan verification failed:{key}')
    _positive(max_trades,'max-trades')
    if max_trades>50000000:raise ValueError('prototype hard cap50million total trades')
    if not math.isfinite(max_output_mib)or not 8<=max_output_mib<=512:raise ValueError('max-output-mib must lie in[8,512]; reserve needed for reports and checkpoints')
    disk_cap=int(max_output_mib*2**20);reserve=8*2**20
    if plan['approx_graph_bytes_total']+reserve>disk_cap:
        return {'status':'inconclusive_output_size_limit','plan':plan,'max_output_MiB':max_output_mib,'created_job':False}
    if stop_after is not None:_positive(stop_after,'stop-after')
    if not math.isfinite(max_seconds)or max_seconds<=0 or not math.isfinite(max_rss_mib)or max_rss_mib<=0:raise ValueError('wall-time and RSS limits must be positive finite')
    folder=Path(folder)
    if plan['total_attempted_pair_trades']>max_trades:
        return {'status':'inconclusive_trade_limit','plan':plan,'max_trades':max_trades,'created_job':False}
    if plan['config']['backend']=='networkit'and environment()['packages']['networkit']!='11.2.2':
        raise ValueError('backend audit requires installedNetworKit11.2.2')
    if not resume:
        if folder.exists()and any(folder.iterdir()):raise ValueError('output directory is nonempty; choose another directory or use resume')
        folder.mkdir(parents=True,exist_ok=True)
        plan=dict(plan);plan['environment']=environment();plan['created_utc']=utc()
        scientific={k:plan[k]for k in ['config','input','certificate_plan','source_hashes','source_commit','environment']}
        plan['job_fingerprint']=digest(canonical(scientific));atomic(folder/'plan.json',plan);atomic(folder/'labels.json',plan['input']['labels'])
    else:
        if plan['source_hashes']!=source_hashes()or plan['environment']!=environment():raise ValueError('resume requires identical source hashes, Python/platform and dependency versions')
        verify_stored_plan(folder,plan)
    lock=_lock(folder,recover_stale_lock);meter=None
    try:
        completed=_verify_outputs(folder,plan);meter=Meter(max_seconds,max_rss_mib,folder);initial=len(completed)
        record={'status':'running','requested_outputs':plan['config']['samples'],'completed_outputs':len(completed),'started_utc':utc()}
        atomic(folder/'status.json',record)
        try:
            for index in range(len(completed),plan['config']['samples']):
                if stop_after is not None and index-initial>=stop_after:raise Paused('requested pause after completed outputs')
                start=time.perf_counter();seed=plan['config']['seed']+index
                graph=_one(plan['input']['graph'],plan['certificate_plan'],seed,plan['config']['backend'],meter)
                result={'status':'completed_conditional_certificate','index':index,'seed':seed,'graph':graph,
                   'certificate':plan['certificate_plan'],'job_fingerprint':plan['job_fingerprint'],'graph_sha256':digest(canonical(graph)),
                   'sampling_seconds':time.perf_counter()-start}
                if folder_bytes(folder)+len(canonical(result))+1+reserve>disk_cap:raise Paused('output-size guard reached; unfinished output discarded; increase --max-output-mib to resume')
                atomic(folder/f'graph-{index:06d}.json',result);completed.append(f'graph-{index:06d}.json')
                record['completed_outputs']=len(completed);atomic(folder/'status.json',record)
            record['status']='completed_conditional_certificate'
        except(KeyboardInterrupt,Paused)as ex:
            record.update(status='paused_incomplete',reason=str(ex)or'keyboard cancellation; unfinished output discarded',inference_available=False)
        except Exception as ex:
            record.update(status='failed_incomplete',reason=str(ex),error_type=type(ex).__name__,inference_available=False)
        record.update(completed_outputs=len(completed),finished_utc=utc(),resources=meter.data())
        atomic(folder/'status.json',record)
        attempts=folder/'attempts.jsonl'
        with attempts.open('a',encoding='utf-8')as handle:handle.write(json.dumps(record)+'\n')
        from .report import write_report
        write_report(folder,plan,record)
        record['committed_job_bytes']=folder_bytes(folder);record['max_output_MiB']=max_output_mib
        atomic(folder/'status.json',record)
        return record
    finally:
        if lock.exists():lock.unlink()

def resume_job(folder,**limits):
    folder=Path(folder);return run_job(load(folder/'plan.json'),folder,resume=True,**limits)
