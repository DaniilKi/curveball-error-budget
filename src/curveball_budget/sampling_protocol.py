"""CBSAMPLE1 byte boundary. Diagnostic validation, not a formal refinement proof."""
from dataclasses import dataclass
import math,re
from .arithmetic_invocation import InvocationError

MAX_REQUEST=4096
MAX_ENTROPY=262144
MAX_RESPONSE=262144
NAT=re.compile(r'(0|[1-9][0-9]*)\Z')
FIELDS=('n','p','q','k','trades','b','cap','eta_num','eta_den','alpha_num','alpha_den')
CAPS=(26,10**12,10**12,4096,1024,32,128,10**12,10**12,10**12,10**12)
@dataclass(frozen=True)
class Request:
 n:int;p:int;q:int;k:int;trades:int;b:int;cap:int
 eta_num:int;eta_den:int;alpha_num:int;alpha_den:int
 edges:tuple[tuple[int,int],...]

def nat(s):
 if not isinstance(s,str) or len(s)>13 or NAT.fullmatch(s) is None:
  raise InvocationError('noncanonical_natural')
 return int(s)

def edge_wire(edges):return ','.join(f'{u}:{v}' for u,v in edges) or '_'
def parse_edges(token,n):
 if token=='_':return ()
 if len(token)>4096:raise InvocationError('edge_resource_cap')
 es=[]
 for item in token.split(','):
  pair=item.split(':')
  if len(pair)!=2:raise InvocationError('malformed_edges')
  u,v=map(nat,pair)
  if not 0<=u<v<n:raise InvocationError('invalid_graph')
  es.append((u,v))
 if len(es)>math.comb(n,2) or len(set(es))!=len(es):raise InvocationError('invalid_graph')
 return tuple(es)

def encode_request(r):
 return ('CBSAMPLE1 sample '+' '.join(str(getattr(r,k)) for k in FIELDS)+' '+edge_wire(r.edges)+'\n').encode('ascii')

def reservations(r):
 pair_count=math.comb(r.n,2)
 pair_width=(pair_count-1).bit_length()
 max_subset=math.comb(r.n-2,(r.n-2)//2)
 subset_width=(max_subset-1).bit_length()
 pair_bits=8*((pair_width*r.cap+7)//8)
 subset_bits=8*((subset_width*r.cap+7)//8)
 return {'pair_count':pair_count,'pair_width':pair_width,'subset_max_count':max_subset,
         'subset_max_width':subset_width,'pair_reserved_bits':pair_bits,
         'subset_reserved_bits':subset_bits,'trade_reserved_bytes':(pair_bits+subset_bits)//8,
         'entropy_bytes':r.b*r.trades*(pair_bits+subset_bits)//8}

def parse_request(wire):
 if not isinstance(wire,bytes) or len(wire)>MAX_REQUEST:raise InvocationError('malformed_request')
 try:tokens=wire.decode('ascii').removesuffix('\n').split(' ')
 except UnicodeError as e:raise InvocationError('malformed_request') from e
 if len(tokens)!=14 or tokens[:2]!=['CBSAMPLE1','sample']:raise InvocationError('malformed_request')
 values=tuple(nat(x) for x in tokens[2:13])
 if any(v>c for v,c in zip(values,CAPS)):raise InvocationError('resource_cap')
 n,p,q,k,t,b,cap,en,ed,an,ad=values
 if n<4 or t==0 or b==0 or cap==0:raise InvocationError('unsupported_domain')
 r=Request(*values,parse_edges(tokens[13],n))
 if encode_request(r)!=wire:raise InvocationError('malformed_request')
 if reservations(r)['entropy_bytes']>MAX_ENTROPY:raise InvocationError('entropy_resource_cap')
 if not arithmetic_plan(r):raise InvocationError('invalid_arithmetic_plan')
 return r

def degrees(n,edges):
 d=[0]*n
 for u,v in edges:d[u]+=1;d[v]+=1
 return tuple(d)

def triangles(n,edges):
 es=set(edges)
 return sum((i,j) in es and (i,k) in es and (j,k) in es
  for i in range(n) for j in range(i+1,n) for k in range(j+1,n))

def budget_predicate(r):
 c=math.comb(r.n,2);m=len(r.edges)
 return (0<r.p and 2*r.p<r.q and m<=c and r.trades==c*r.k and
  math.comb(c,m)*r.q*r.q<=4*r.p*r.p*2**(2*r.k))

def arithmetic_plan(r):
 return (budget_predicate(r) and r.eta_den>0 and r.alpha_den>0 and
  0<r.alpha_num<r.alpha_den and r.eta_num*r.alpha_den<r.alpha_num*r.eta_den and
  r.b*r.p*r.eta_den<=r.eta_num*r.q)

def rank_predicate(r,exceed):
 en,ed,an,ad=r.eta_num,r.eta_den,r.alpha_num,r.alpha_den
 return (0<r.b and exceed<=r.b and ed>0 and ad>0 and 0<an<ad and en*ad<an*ed and
  (exceed+1)*ad*ed+(r.b+1)*en*ad<=an*(r.b+1)*ed)

def encode_response(r,graphs):
 stats=tuple(triangles(r.n,g) for g in graphs);obs=triangles(r.n,r.edges)
 exc=sum(s>=obs for s in stats)
 return (f'CBSAMPLE1 result {r.n} {len(r.edges)} {r.trades} {r.b} {r.b*r.trades} {obs} {exc} '
  f'{str(budget_predicate(r)).lower()} {str(rank_predicate(r,exc)).lower()} '
  +','.join(map(str,stats))+' '+';'.join(edge_wire(g) for g in graphs)+'\n').encode('ascii')

def parse_response(r,stdout,stderr,code):
 if not isinstance(stdout,bytes) or len(stdout)>MAX_RESPONSE:raise InvocationError('response_resource_cap')
 if stderr:raise InvocationError('unexpected_stderr')
 if code!=0:
  allowed={2:{b'CBSAMPLE1 error malformed-request\n',b'CBSAMPLE1 error argument-count\n',b'CBSAMPLE1 error invalid-arithmetic-plan\n'},
   3:{b'CBSAMPLE1 error entropy-size\n',b'CBSAMPLE1 error entropy-or-draw\n',b'CBSAMPLE1 error incomplete-batch\n'},
   4:{b'CBSAMPLE1 error io-failure\n'}}
  if stdout in allowed.get(code,set()):raise InvocationError('native_sampling_failure',stdout.decode('ascii').strip())
  raise InvocationError('native_process_failure')
 try:tokens=stdout.decode('ascii').removesuffix('\n').split(' ')
 except UnicodeError as e:raise InvocationError('noncanonical_response') from e
 if len(tokens)!=13 or tokens[:2]!=['CBSAMPLE1','result']:raise InvocationError('noncanonical_response')
 n,m,t,b,count,obs,exc=map(nat,tokens[2:9])
 if (n,m,t,b,count)!=(r.n,len(r.edges),r.trades,r.b,r.b*r.trades):raise InvocationError('incomplete_batch')
 if tokens[9] not in ('true','false') or tokens[10] not in ('true','false'):raise InvocationError('noncanonical_response')
 stats=tuple(map(nat,tokens[11].split(',')))
 graphs=tuple(parse_edges(s,r.n) for s in tokens[12].split(';'))
 if len(stats)!=r.b or len(graphs)!=r.b:raise InvocationError('incomplete_batch')
 if any(degrees(r.n,g)!=degrees(r.n,r.edges) for g in graphs):raise InvocationError('degree_diagnostic_mismatch')
 if encode_response(r,graphs)!=stdout:raise InvocationError('response_diagnostic_mismatch')
 return {'n':n,'m':m,'trades_per_chain':t,'replicates':b,'attempted_trades':count,
  'observed_triangles':obs,'replicate_triangles':stats,'exceed_count':exc,
  'budget_predicate_passed':tokens[9]=='true','rank_predicate_passed':tokens[10]=='true',
  'output_graphs':graphs,'degree_diagnostic_passed':True,'triangle_diagnostic_passed':True}
