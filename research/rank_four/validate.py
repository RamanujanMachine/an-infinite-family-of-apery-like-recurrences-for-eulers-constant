"""Independent Barnes-residue seeds and positive-series checks using exact walks.

Uses 400-digit arithmetic. This is numerical evidence, not a convergence proof.
"""
import json,math
from pathlib import Path
import sympy as sp
import mpmath as mp
from sympy.abc import n
from ramanujantools import Position
from ramanujantools.cmf import MeijerG
mp.mp.dps=400
ROOT=Path(__file__).resolve().parent
def num(x):
 a,b=sp.fraction(x);return mp.mpf(int(a))/mp.mpf(int(b))
def origin(z,k):
 H=mp.mpf(0);H2=mp.mpf(0);H3=mp.mpf(0);fac=mp.mpf(1);out=[[] for _ in range(4)]
 for ell in range(5000):
  L=H-mp.euler-mp.log(z)+2j*mp.pi*k
  Q=(7*mp.zeta(2)+H2)/2;C=(H3-mp.zeta(3))/3
  B=[1,L,L*L/2+Q,L**3/6+L*Q+C]
  terms=[fac*sum(math.comb(j,a)*mp.mpf(ell)**(j-a)*(-1)**a*B[3-a] for a in range(j+1)) for j in range(4)]
  for j in range(4):out[j].append(terms[j])
  if ell>30 and max(abs(x) for x in terms)<mp.eps**mp.mpf('1.05'):break
  fac*=z/(ell+1);H+=mp.mpf(1)/(ell+1);H2+=mp.mpf(1)/(ell+1)**2;H3+=mp.mpf(1)/(ell+1)**3
 return [mp.fsum(v) for v in out]
def positive(n,m,A,z):
 terms=[[] for _ in range(4)];t=mp.mpf(1)
 for k in range(10000):
  for j in range(4):terms[j].append(t*(m*n+k)**j)
  ratio=z*mp.fprod(a*n+k+1 for a in A)/(k+1)**4
  if k>30 and ratio<1 and t<mp.eps**mp.mpf('1.05'):break
  t*=ratio
 scale=z**(m*n)*mp.fprod(mp.gamma(a*n+1) for a in A)
 return [scale*mp.fsum(v) for v in terms]
axes=sp.symbols('a0 a1 a2 b0 b1 b2 b3');results=[]
for label,t,zs in [('base',(0,0,0,1,1,1,1),sp.Integer(1)),('unequal',(-1,0,0,1,1,1,1),sp.Rational(1,4)),('m2',(0,0,0,2,2,2,2),sp.Integer(1))]:
 z=num(zs);m=t[3];A=[m-a for a in t[:3]]
 M=MeijerG(m=4,n=3,p=3,q=4,z=zs).trajectory_matrix(Position(dict(zip(axes,t))),Position(dict.fromkeys(axes,0)))
 seeds={k:origin(z,k) for k in [-1,0,1,2]}
 pos0=[mp.exp(z),z*mp.exp(z),(z*z+z)*mp.exp(z),(z**3+3*z*z+z)*mp.exp(z)]
 comb=[(seeds[2][j]-3*seeds[1][j]+3*seeds[0][j]-seeds[-1][j])/(2j*mp.pi)**3 for j in range(4)]
 print(label,'origin positive-branch identity error:',mp.nstr(max(abs(a-b) for a,b in zip(comb,pos0)),6),flush=True)
 for N,W in zip([10,40,100,200],M.walk({n:1},[10,40,100,200],{n:0})):
  WW=[[num(W[i,j]) for j in range(4)] for i in range(4)]
  vecs={k:[mp.fsum(seeds[k][i]*WW[i][j] for i in range(4)) for j in range(4)] for k in [0,1,2]}
  pos=[mp.fsum(pos0[i]*WW[i][j] for i in range(4)) for j in range(4)]
  direct=positive(N,m,A,z)
  err=max(abs(a/b-1) for a,b in zip(pos,direct))
  H=z**(m*N)*mp.fprod(mp.gamma(a*N+1) for a in A);R=mp.mpf(N)**mp.mpf('.75');c=(mp.fprod(A)*z)**mp.mpf('.25')
  obs={'case':label,'n':N,'positive_propagation_relative_error':mp.nstr(err,8),'log_norm_over_H_div_n_3_4':{str(k):mp.nstr(mp.log(max(abs(x) for x in v)/H)/R,12) for k,v in vecs.items()},'positive_log_norm_over_H_div_n_3_4':mp.nstr(mp.log(max(abs(x) for x in pos)/H)/R,12),'target_4c':mp.nstr(4*c,12)}
  # Recover moments of x from moments of mn-x.
  for k,v in list(vecs.items())+[('positive',pos)]:
   obs['normalized_x_moments_'+str(k)]=[mp.nstr(mp.fsum(math.comb(j,a)*mp.mpf(m*N)**(j-a)*(-1)**a*v[a] for a in range(j+1))/(R**j*v[0]),10) for j in [1,2,3]]
  print(obs,flush=True);results.append(obs)
  if N in [10] and label=='base':
   g=mp.meijerg([[0,0,0],[]],[[N,N,N,N],[]],z)
   print('direct canonical Meijer G relative error:',mp.nstr(abs(vecs[0][0]/g-1),8),flush=True)
(ROOT/'validation.json').write_text(json.dumps(results,indent=2))
