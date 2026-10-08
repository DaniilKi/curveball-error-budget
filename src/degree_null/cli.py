import argparse,csv,json,sys
from pathlib import Path
from .inputs import read_network
from .jobs import make_plan,run_job,resume_job,load,_verify_outputs,verify_stored_plan

def _input(parser):
    parser.add_argument('--input',required=True);parser.add_argument('--format',choices=['csv','edgelist'],default='csv')
    parser.add_argument('--vertices',help='complete vertex universe: JSON array of strings or one label per line; includes isolates')
    parser.add_argument('--directed',action='store_true');parser.add_argument('--weighted',action='store_true')
    parser.add_argument('--samples',type=int,required=True);parser.add_argument('--tv',required=True,help='total batchTV budget as fraction, e.g.1/100')
    parser.add_argument('--seed',type=int,default=131001);parser.add_argument('--backend',choices=['networkit','reference'],default='networkit')
    parser.add_argument('--statistic',choices=['triangles']);parser.add_argument('--predeclared',action='store_true')
    parser.add_argument('--alpha',default='1/20',help='overall type-I target; raw rank cutoff is alpha minus totalTV')
def _limits(parser):
    parser.add_argument('--max-trades',type=int,default=10000000);parser.add_argument('--max-seconds',type=float,default=60)
    parser.add_argument('--max-rss-mib',type=float,default=256);parser.add_argument('--max-output-mib',type=float,default=128)
    parser.add_argument('--stop-after',type=int,help='pause after this many additional completed graphs')
    parser.add_argument('--recover-stale-lock',action='store_true')
def main(argv=None):
    parser=argparse.ArgumentParser(description='Private research comparison networks preserving every labeled node degree. Guarantees conditional on manuscript and ideal randomness.')
    sub=parser.add_subparsers(dest='command',required=True)
    p=sub.add_parser('plan',help='inspect trade budget and rough runtime without sampling');_input(p)
    p=sub.add_parser('run',help='create a new bounded streamed job');_input(p);_limits(p);p.add_argument('--output',required=True)
    p=sub.add_parser('resume',help='verify saved job then replay unfinished output from original input');p.add_argument('--job',required=True);_limits(p)
    p=sub.add_parser('export',help='export one verified completed graph to labeled CSV');p.add_argument('--job',required=True);p.add_argument('--index',type=int,required=True);p.add_argument('--output',required=True)
    args=parser.parse_args(argv)
    try:
        if args.command=='export':
            folder=Path(args.job);plan=verify_stored_plan(folder,load(folder/'plan.json'));completed=_verify_outputs(folder,plan)
            if args.index<0 or args.index>=len(completed):raise ValueError('index is not a completed graph')
            target=Path(args.output)
            if target.exists():raise ValueError('export output exists; choose another path')
            graph=load(folder/completed[args.index])['graph'];labels=plan['input']['labels']
            with target.open('x',encoding='utf-8',newline='')as stream:
                writer=csv.writer(stream);writer.writerow(['source','target'])
                for a,b in graph['edges']:writer.writerow([labels[a],labels[b]])
            print(json.dumps({'status':'exported','path':str(target.resolve()),'isolates_mapping':str((folder/'labels.json').resolve()),'warning':'edgeCSV has no isolate rows; retain labels.json for complete node universe'}));return 0
        if args.command in ['plan','run']:
            if args.statistic and not args.predeclared:raise ValueError('inferential demo requires --predeclared; select statistic before inspecting it or choosing results')
            network=read_network(args.input,args.format,args.vertices,args.directed,args.weighted)
            plan=make_plan(network,args.samples,args.tv,args.seed,args.backend,args.statistic,args.alpha)
        else:plan=load(Path(args.job)/'plan.json')
        overview={k:plan[k]for k in ['total_attempted_pair_trades','rough_runtime_seconds','runtime_estimate_scope','approx_graph_bytes_total','assurance']}
        overview.update(samples=plan['config']['samples'],joint_tv=plan['config']['joint_tv'],nodes=plan['input']['graph']['n'])
        if plan.get('coarse_rank_warning'):overview['warning']='minimum rankscore exceeds alpha-minus-TV cutoff; this batch cannot reject at overallalpha'
        if args.command=='plan':print(json.dumps(plan,indent=2));return 0
        print('Plan before sampling: '+json.dumps(overview),file=sys.stderr,flush=True)
        limits={k:getattr(args,k)for k in ['max_trades','max_seconds','max_rss_mib','max_output_mib','stop_after','recover_stale_lock']}
        result=run_job(plan,args.output,**limits)if args.command=='run'else resume_job(args.job,**limits)
        print(json.dumps(result,indent=2));return 0 if result['status']=='completed_conditional_certificate'else 2
    except Exception as ex:
        print(json.dumps({'status':'error','error_type':type(ex).__name__,'error':str(ex)}),file=sys.stderr);return 2
if __name__=='__main__':raise SystemExit(main())
