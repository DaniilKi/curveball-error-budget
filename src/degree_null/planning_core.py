"""Factored v0.2.0 planning/validation core, with unchanged public results.

Copyright 2026 DaniilKi contributors. SPDX-License-Identifier: Apache-2.0
Source: published kernel.py at 9319b8289617a6a08aeb528000bddff4da7ca121.
Conditional operator input: OpenAI/math family131, fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
This factorization adds no mathematical or backend assurance.
"""
import math
from fractions import Fraction

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
