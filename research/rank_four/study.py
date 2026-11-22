"""Formal recurrence evidence for rank four; run with the project Python dependencies."""
import json,signal,time
from pathlib import Path
import sympy as sp
from sympy.abc import n
from ramanujantools import Position,LinearRecurrence
from ramanujantools.cmf import MeijerG
ROOT=Path(__file__).resolve().parent
axes=sp.symbols('a0 a1 a2 b0 b1 b2 b3')
cases=[('base_z1',(0,0,0,1,1,1,1),sp.Integer(1)),('base_z1_16',(0,0,0,1,1,1,1),sp.Rational(1,16)),('base_z16',(0,0,0,1,1,1,1),sp.Integer(16)),('unequal_upper',(-1,0,0,1,1,1,1),sp.Integer(1)),('equal_lower_2',(0,0,0,2,2,2,2),sp.Integer(1))]
def timeout(sig,frame):raise TimeoutError('asymptotics timed out')
signal.signal(signal.SIGALRM,timeout)
results=[]
for label,t,z in cases:
 begin=time.monotonic();print('START',label,flush=True)
 M=MeijerG(m=4,n=3,p=3,q=4,z=z).trajectory_matrix(Position(dict(zip(axes,t))),Position(dict.fromkeys(axes,0)))
 rec=LinearRecurrence(M)
 # RT relations use backward shifts; normalize the fourth-order time index.
 rec=LinearRecurrence([c.subs(n,n-4) for c in rec.relation])
 data={'backward_index_shift':-4,'case':label,'trajectory':t,'z':str(z),'matrix':str(M),'recurrence':[str(x) for x in rec.relation],'attempts':[]}
 for precision in [None,32,48]:
  try:
   signal.alarm(30)
   growths=rec.asymptotics(precision=precision)
   signal.alarm(0)
   data['growths']=[str(sp.expand_power_exp(g)) for g in growths]
   data['precision']=precision
   print('GROWTHS',label,data['growths'],flush=True)
   break
  except Exception as e:
   signal.alarm(0);data['attempts'].append({'precision':precision,'error':type(e).__name__+': '+str(e)})
   print('RETRY',label,precision,type(e).__name__,flush=True)
 data['seconds']=time.monotonic()-begin
 results.append(data);(ROOT/'formal_results.json').write_text(json.dumps(results,indent=2))
 print('DONE',label,round(data['seconds'],2),flush=True)
