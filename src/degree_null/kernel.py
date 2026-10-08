"""Conditional finite-TV certificate for the existing undirected Curveball kernel.

Theorem: openai/math fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, family131.
No uniformity claim for a finite PRNG seed, global trades, forced successes,
or connected-only/weighted/directed graph spaces. Units are attempted pair trades.
"""
from __future__ import annotations
import argparse, json, math, os, random, time
from fractions import Fraction
from pathlib import Path

SOURCE_COMMIT = 'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb'

def validate_graph(spec):
    if not isinstance(spec, dict): raise ValueError('graph must be a JSON object')
    if spec.get('directed', False) or spec.get('weighted', False) or 'weights' in spec:
        raise ValueError('only unweighted undirected simple graphs are supported')
    n=spec.get('n')
    if type(n) is not int or not 0<=n<=1000: raise ValueError('n must be an integer in [0,1000] for this bounded prototype')
    edges=spec.get('edges')
    if not isinstance(edges, list): raise ValueError('edges must be a list of endpoint pairs')
    seen=set(); adj=[set() for _ in range(n)]
    for e in edges:
        if not isinstance(e,(list,tuple)) or len(e)!=2: raise ValueError('edge must have two endpoints; weights are unsupported')
        a,b=e
        if type(a) is not int or type(b) is not int or not(0<=a<n and 0<=b<n): raise ValueError('endpoints must be contiguous integer labels in [0,n)')
        if a==b: raise ValueError('self-loops unsupported')
        key=tuple(sorted((a,b)))
        if key in seen: raise ValueError('duplicate/multiple edges unsupported')
        seen.add(key);adj[a].add(b);adj[b].add(a)
    return adj

def edges_from_adj(adj): return [[i,j] for i,a in enumerate(adj) for j in sorted(a) if i<j]

def realize_degrees(degrees):
    if not isinstance(degrees,list) or len(degrees)>1000: raise ValueError('degrees must be a list of at most1000 integers')
    n=len(degrees)
    if any(type(d) is not int or not 0<=d<n for d in degrees) or sum(degrees)%2: raise ValueError('invalid degree vector')
    remaining=list(degrees);edges=[]
    while True:
        order=sorted(range(n),key=lambda i:(-remaining[i],i));a=order[0] if n else 0
        if not n or remaining[a]==0: break
        d=remaining[a];targets=[i for i in order[1:] if remaining[i]>0][:d]
        if len(targets)!=d: raise ValueError('degree vector is not graphical')
        remaining[a]=0
        for b in targets: remaining[b]-=1;edges.append([a,b])
    spec={'n':n,'edges':edges};adj=validate_graph(spec)
    if [len(a) for a in adj]!=degrees: raise ValueError('degree vector is not graphical')
    return spec

def forced_unique(degrees):
    """Sufficient unique-realization test by deterministic isolated/universal peeling."""
    d=list(degrees)
    while d:
        if 0 in d: d.remove(0);continue
        if len(d)-1 in d:
            d.remove(len(d)-1);d=[v-1 for v in d];continue
        return False
    return True

def parse_epsilon(value):
    if len(str(value))>1000: raise ValueError('epsilon representation exceeds resource limit')
    e=Fraction(value)
    if not 0<e<Fraction(1,2): raise ValueError('epsilon must lie strictly between0 and1/2')
    return e

def certificate(degrees, epsilon='1/10'):
    # Public API validates graphicality independently of any caller-supplied claim.
    realize_degrees(degrees)
    e=parse_epsilon(epsilon);n=len(degrees);C=n*(n-1)//2;m=sum(degrees)//2
    if forced_unique(degrees): u=v=t=0;unique=True
    else:
        if C<2: raise ValueError('nontrivial graph space cannot have fewer than2 pairs')
        bound=math.comb(C,m);u=(bound-1).bit_length();v=0
        q=1/(2*e)
        while (q.denominator<<v)<q.numerator: v+=1
        blocks=(u+1)//2+v
        if bound*e.denominator**2>4*e.numerator**2*(1<<(2*blocks)):
            raise RuntimeError('exact upward-rounding certificate failed')
        t=C*blocks;unique=False
    return {'source_commit':SOURCE_COMMIT,'theorem_assurance':'conditional on manuscript pair-resampling gap; no independent Lean compilation',
      'target':'uniform labeled simple undirected graphs with exactly this degree vector; no connectedness restriction',
      'epsilon':str(e),'n':n,'edges':m,'degrees':list(degrees),'unordered_vertex_pairs':C,
      'state_count_upper_formula':'1 via forced unique realization certificate' if unique else f'binom({C},{m})','state_count_log2_ceiling':u,
      'forced_unique':unique,'binary_error_exponent':v,'attempted_pair_trades':t,
      'exact_integer_rounding_check':True,
      'bound_derivation':'K>=0,gap>=1/C; TV<=.5sqrt(M)(1-1/C)^t; (1-1/C)^C<=1/2; upward exact integer binary budget',
      'randomness_assumption':'independent uniform pair/subset draws; finite seeded PRNG is a reproducible implementation, not a mathematical exact-uniform oracle'}

def reference_trade(adj, i, j, rng):
    left=adj[i]-adj[j]-{j};right=adj[j]-adj[i]-{i}
    pool=sorted(left|right);chosen=set(rng.sample(pool,len(left)));other=set(pool)-chosen
    for v in left: adj[v].remove(i)
    for v in right: adj[v].remove(j)
    adj[i].difference_update(left);adj[j].difference_update(right)
    adj[i].update(chosen);adj[j].update(other)
    for v in chosen: adj[v].add(i)
    for v in other: adj[v].add(j)
    return chosen!=left

def reference_run(adj, trades, seed):
    rng=random.Random(seed);n=len(adj);changed=0
    for _ in range(trades):
        i=rng.randrange(n);j=rng.randrange(n-1);j+=j>=i
        changed+=reference_trade(adj,i,j,rng)
    return adj,{'changed_pair_trades':changed,'seed':seed,'random_engine':'Python random.Random MT19937'}

def get_networkit():
    # Set before importing numpy/scipy/native libraries; caller must also limit env.
    for k in ['OMP_NUM_THREADS','OPENBLAS_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS']:
        os.environ[k]='1'
    import networkit as nk
    nk.setNumberOfThreads(1)
    if nk.__version__!='11.2.2': raise ValueError('compiled backend audit currently covers NetworKit11.2.2 only')
    return nk

def networkit_run(adj,trades,seed,chunk=10000):
    if type(chunk) is not int or chunk<1: raise ValueError('chunk must be positive')
    if not trades:return adj,{'seed':seed,'backend_version':'11.2.2','skipped_zero_trade_backend':True}
    nk=get_networkit();nk.setSeed(seed,False);g=nk.Graph(len(adj),weighted=False,directed=False)
    for a,b in edges_from_adj(adj):g.addEdge(a,b)
    cb=nk.randomization.Curveball(g);remaining=trades;chunks=0
    while remaining:
        count=min(chunk,remaining)
        pairs=nk.randomization.CurveballUniformTradeGenerator(count,len(adj)).generate()
        if len(pairs)!=count: raise RuntimeError('trade generator length mismatch')
        cb.run(pairs);remaining-=count;chunks+=1
    out=cb.getGraph();result=[set(out.iterNeighbors(i)) for i in range(len(adj))]
    return result,{'seed':seed,'backend_version':nk.__version__,'chunks':chunks,'chunk_size':chunk,
       'affected_edges_backend_diagnostic':cb.getNumberOfAffectedEdges(),
       'affected_edges_interpretation':'backend diagnostic; not counted Markov steps and may describe only latest run'}

def sample_graph(spec,epsilon='1/10',seed=131001,backend='networkit',max_trades=10000000,chunk=10000):
    if type(seed) is not int or not 0<=seed<2**64:raise ValueError('seed must be an unsigned64-bit integer')
    adj=validate_graph(spec);degrees=[len(a) for a in adj];cert=certificate(degrees,epsilon)
    if cert['attempted_pair_trades']>max_trades:return {'status':'inconclusive_resource_limit','certificate_plan':cert,'max_trades':max_trades}
    start=time.perf_counter()
    if backend=='reference':out,meta=reference_run(adj,cert['attempted_pair_trades'],seed)
    elif backend=='networkit':out,meta=networkit_run(adj,cert['attempted_pair_trades'],seed,chunk)
    else:raise ValueError('unsupported backend')
    graph={'n':len(out),'edges':edges_from_adj(out)};checked=validate_graph(graph)
    if [len(a) for a in checked]!=degrees:raise RuntimeError('degree invariant failed')
    return {'status':'completed_conditional_certificate','certificate':cert,'backend':backend,'sampling_seconds':time.perf_counter()-start,'backend_metadata':meta,'graph':graph}

def sample_batch(spec,samples=99,joint_epsilon='1/100',seed=131001,backend='networkit',max_trades=10000000,chunk=10000):
    if type(samples) is not int or not 1<=samples<=1000:raise ValueError('samples must be an integer in[1,1000]')
    if type(seed) is not int or not 0<=seed<=2**64-samples:raise ValueError('batch seeds must fit unsigned64-bit integers')
    total=parse_epsilon(joint_epsilon);adj=validate_graph(spec);per=total/samples
    plan=certificate([len(a) for a in adj],per);total_trades=samples*plan['attempted_pair_trades']
    contract={'joint_epsilon':str(total),'per_output_epsilon':str(per),'samples':samples,'total_attempted_pair_trades':total_trades,
      'restart_policy':'fresh restart from original validated graph for each output; separate seed seed+output_index',
      'ideal_target':'IID uniform labeled simple graphs with original fixed degrees',
      'joint_bound':'conditional on manuscript and independent ideal uniform draws: total variation of batch <=sum per-output error',
      'finite_prng_limitation':'distinct deterministic seeds do not prove independence or exact uniform draws'}
    if total_trades>max_trades:return {'status':'inconclusive_resource_limit','joint_contract':contract,'certificate_plan':plan,'max_trades':max_trades}
    start=time.perf_counter();outputs=[]
    for j in range(samples):
        result=sample_graph(spec,str(per),seed+j,backend,max_trades,chunk)
        if result['status']!='completed_conditional_certificate':raise RuntimeError('batch constituent failed')
        outputs.append(result)
    return {'status':'completed_conditional_certificate','joint_contract':contract,'certificate_plan':plan,'backend':backend,
      'batch_sampling_seconds':time.perf_counter()-start,'outputs':outputs}

def main():
    p=argparse.ArgumentParser(description=__doc__);src=p.add_mutually_exclusive_group(required=True)
    src.add_argument('--input',type=Path);src.add_argument('--degrees',help='comma-separated labeled degree vector')
    p.add_argument('--epsilon',default='1/10');p.add_argument('--seed',type=int,default=131001)
    p.add_argument('--backend',choices=['networkit','reference'],default='networkit');p.add_argument('--max-trades',type=int,default=10000000)
    p.add_argument('--chunk',type=int,default=10000);p.add_argument('--output',type=Path)
    p.add_argument('--samples',type=int,default=1);p.add_argument('--joint-epsilon',help='total batchTV budget; default uses --epsilon')
    args=p.parse_args()
    try:
        spec=json.loads(args.input.read_text(encoding='utf-8')) if args.input else realize_degrees([int(x) for x in args.degrees.split(',')])
        result=sample_batch(spec,args.samples,args.joint_epsilon or args.epsilon,args.seed,args.backend,args.max_trades,args.chunk) if args.samples>1 else sample_graph(spec,args.joint_epsilon or args.epsilon,args.seed,args.backend,args.max_trades,args.chunk)
    except Exception as ex:result={'status':'error','error_type':type(ex).__name__,'error':str(ex)}
    text=json.dumps(result,indent=2)
    if args.output:args.output.write_text(text+'\n',encoding='utf-8')
    else:print(text)
    return 0 if result['status']=='completed_conditional_certificate' else 2

if __name__=='__main__':raise SystemExit(main())
