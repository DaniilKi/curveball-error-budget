"""Bounded exact/input/restart tests. No large empirical discovery claims."""
import contextlib,copy,io,itertools,json,sys,tempfile,time,unittest
from fractions import Fraction
from pathlib import Path
from unittest.mock import patch
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT/'src'))
from degree_null import read_network,make_plan,run_job,resume_job
from degree_null import jobs,kernel
from degree_null.cli import main as cli

class Tests(unittest.TestCase):
    def setUp(self):self.tmp=tempfile.TemporaryDirectory();self.folder=Path(self.tmp.name)
    def tearDown(self):self.tmp.cleanup()
    def network(self,csv='source,target\na,b\nc,d\n',vertices=None):
        path=self.folder/'input.csv';path.write_text(csv,encoding='utf-8',newline='')
        vp=None
        if vertices is not None:vp=self.folder/'vertices.json';vp.write_text(json.dumps(vertices),encoding='utf-8')
        return read_network(path,vertices=vp)
    def test_inputs_and_labels(self):
        net=self.network('source,target\n001,"Alice, Jr."\n', ['001','Alice, Jr.','孤立'])
        self.assertEqual(net['labels'],['001','Alice, Jr.','孤立']);self.assertEqual(net['degrees'],[1,1,0])
        for data in ['source,target\na,a\n','source,target\na,b\nb,a\n','source,target,weight\na,b,2\n','source,target\na,b,c\n','source,target\n,b\n']:
            with self.assertRaises(ValueError):self.network(data)
        with self.assertRaises(ValueError):self.network(vertices=['a','a'])
        with self.assertRaises(ValueError):self.network(vertices=['a','b'])
        net=self.network()
        for flag in ['directed','weighted']:
            with self.assertRaises(ValueError):read_network(self.folder/'input.csv',**{flag:True})
    def test_plan_validation(self):
        net=self.network()
        for count in [0,-1,True,1.5,1001]:
            with self.assertRaises(ValueError):make_plan(net,count,'1/100')
        for epsilon in ['0','-1','1/2','nan','1e-1000000000']:
            with self.assertRaises((ValueError,ZeroDivisionError)):make_plan(net,1,epsilon)
        with self.assertRaises(ValueError):make_plan(net,19,'1/100',statistic='triangles',alpha='1/1000')
        self.assertEqual(make_plan(net,99,'1/100',statistic='triangles')['config']['raw_rank_cutoff'],'1/25')
        for seed in [-1,True,2**64]:
            with self.assertRaises(ValueError):make_plan(net,2,'1/100',seed=seed)
        bad=copy.deepcopy(net);bad['graph']['edges'].append([0,1])
        with self.assertRaises(ValueError):make_plan(bad,2,'1/100')
        plan=make_plan(net,3,'1/100',backend='reference')
        for key,value in [('total_attempted_pair_trades',1),('certificate_plan',kernel.certificate(net['degrees'],'1/10'))]:
            changed=copy.deepcopy(plan);changed[key]=value
            with self.assertRaises(ValueError):run_job(changed,self.folder/'forged')
        plan=make_plan(net,1,'1/100',backend='networkit')
        env=jobs.environment();env['packages']['networkit']='0'
        with patch.object(jobs,'environment',return_value=env):
            with self.assertRaises(ValueError):run_job(plan,self.folder/'wrongversion')
    def test_empty_single_and_unique(self):
        for vertices,edges in [([], 'source,target\n'),(['solo'],'source,target\n'),(['a','b'],'source,target\na,b\n')]:
            net=self.network(edges,vertices);plan=make_plan(net,2,'1/100',backend='reference')
            self.assertEqual(plan['total_attempted_pair_trades'],0)
            target=self.folder/f'job{len(vertices)}';result=run_job(plan,target)
            self.assertEqual(result['status'],'completed_conditional_certificate')
            self.assertEqual(json.loads((target/'labels.json').read_text()),vertices)
    def test_pause_resume_and_rejections(self):
        plan=make_plan(self.network(),4,'1/100',backend='reference');folder=self.folder/'job'
        result=run_job(plan,folder,stop_after=1);self.assertEqual(result['completed_outputs'],1)
        self.assertIsNone(json.loads((folder/'certificate-report.json').read_text())['inference'])
        self.assertIsNone(json.loads((folder/'certificate-report.json').read_text())['joint_tv_contract'])
        original=(folder/'graph-000000.json').read_bytes()
        (folder/'STOP').write_text('pause')
        result=resume_job(folder);self.assertEqual(result['status'],'paused_incomplete')
        (folder/'STOP').unlink();result=resume_job(folder);self.assertEqual(result['completed_outputs'],4)
        self.assertEqual((folder/'graph-000000.json').read_bytes(),original)
        full=self.folder/'full';run_job(plan,full)
        for i in range(4):
            self.assertEqual(jobs.load(folder/f'graph-{i:06d}.json')['graph'],jobs.load(full/f'graph-{i:06d}.json')['graph'])
        mapping=jobs.load(folder/'labels.json');mapping[0]='edited';jobs.atomic(folder/'labels.json',mapping)
        with self.assertRaises(ValueError):resume_job(folder)
        with contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(cli(['export','--job',str(folder),'--index','0','--output',str(self.folder/'bad.csv')]),2)
    def test_limits_and_partial_cancel(self):
        net=self.network();plan=make_plan(net,3,'1/100',backend='reference')
        self.assertEqual(run_job(plan,self.folder/'capped',max_trades=1)['status'],'inconclusive_trade_limit')
        self.assertFalse((self.folder/'capped').exists())
        tiny=run_job(plan,self.folder/'time',max_seconds=1e-9);self.assertEqual(tiny['completed_outputs'],0)
        rss=run_job(plan,self.folder/'rss',max_rss_mib=.01);self.assertEqual(rss['status'],'paused_incomplete')
        original=kernel.reference_trade;counter=[0]
        def interrupt(*args):
            counter[0]+=1
            if counter[0]==4:raise KeyboardInterrupt()
            return original(*args)
        with patch.object(kernel,'reference_trade',side_effect=interrupt):
            result=run_job(plan,self.folder/'interrupt')
        self.assertEqual(result['completed_outputs'],0);self.assertFalse(list((self.folder/'interrupt').glob('graph-*.json')))
        self.assertEqual(resume_job(self.folder/'interrupt')['completed_outputs'],3)
    def test_exact_tiny_uniform_kernel(self):
        # Independent pair-fiber law vs actual reference transition on three matchings.
        states=[[[0,1],[2,3]],[[0,2],[1,3]],[[0,3],[1,2]]]
        key=lambda g:tuple(tuple(x)for x in kernel.edges_from_adj(g))
        index={key(kernel.validate_graph({'n':4,'edges':s})):i for i,s in enumerate(states)}
        matrix=[]
        for state in states:
            row=[Fraction(0)for _ in states];initial=kernel.validate_graph({'n':4,'edges':state})
            for a,b in itertools.combinations(range(4),2):
                left=initial[a]-initial[b]-{b};right=initial[b]-initial[a]-{a};pool=sorted(left|right)
                choices=list(itertools.combinations(pool,len(left)))
                for choice in choices:
                    class Fixed:
                        def sample(self,population,k):
                            assert population==pool and k==len(left);return list(choice)
                    adj=[set(x)for x in initial];kernel.reference_trade(adj,a,b,Fixed())
                    row[index[key(adj)]]+=Fraction(1,6*len(choices))
            matrix.append(row)
        self.assertEqual(matrix,[[Fraction(2,3)if i==j else Fraction(1,6)for j in range(3)]for i in range(3)])
        distribution=[Fraction(1),Fraction(0),Fraction(0)]
        cert=kernel.certificate([1,1,1,1],'1/100')
        for _ in range(cert['attempted_pair_trades']):
            distribution=[sum(distribution[i]*matrix[i][j]for i in range(3))for j in range(3)]
        tv=sum(abs(p-Fraction(1,3))for p in distribution)/2
        self.assertLessEqual(tv,Fraction(1,100))
    def test_compiled_wrapper_matches_audited_kernel(self):
        spec={'n':6,'edges':[[0,1],[1,2],[0,2],[3,4],[4,5],[3,5]]}
        cert=kernel.certificate([2]*6,'1/100')
        class Meter:
            def check(self):pass
        for seed in [131001,131002]:
            graph=jobs._one(spec,cert,seed,'networkit',Meter())
            audited=kernel.sample_graph(spec,'1/100',seed,'networkit')
            self.assertEqual(graph,audited['graph'])

if __name__=='__main__':
    start=time.perf_counter();result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(Tests))
    receipt={'tests':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'passed':result.wasSuccessful(),'wall_seconds':time.perf_counter()-start,'source_hashes':jobs.source_hashes(),
      'scope':'exact tiny law, strict ingestion, planning and interrupted-output full replay; no empirical large-stateTV claim',
      'failure_details':[str(x)for x in result.failures+result.errors]}
    target=ROOT/'evidence';target.mkdir(exist_ok=True);number=len(list(target.glob('tool-tests-*.json')))+1
    (target/f'tool-tests-{number:03d}.json').write_text(json.dumps(receipt,indent=2)+'\n')
    raise SystemExit(0 if result.wasSuccessful()else 1)
