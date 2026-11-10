"""Relance reproductible de l'énumération exhaustive indépendante (sans script Claude).
Python standard + clang++; assertions actives. max n=13, mémoire <250 Mo environ.
"""
from pathlib import Path
import csv,subprocess,sys
root=Path(__file__).resolve().parent
maxn=int(sys.argv[1]) if len(sys.argv)>1 else 13
exe=root/'verif_riordan_chatgpt'
subprocess.run(['clang++','-O3','-std=c++17',str(root/'verif_riordan_chatgpt.cpp'),'-o',str(exe)],check=True)
p=subprocess.run([str(exe),str(maxn)],capture_output=True,text=True,check=True)
(root/'resultats_chatgpt.csv').write_text(p.stdout)
(root/'profils_chatgpt.txt').write_text(p.stderr)
print(p.stdout,end='')
rows=list(csv.DictReader(p.stdout.splitlines()))
a=[0]
for n in range(1,1001):
    value=1+sum(1<<(3*(k-1)//2) for k in range(1,n))
    if n%2==0:
        k=n//2; numer=10*8**(k-1)+4
    else:
        k=(n-1)//2; numer=3*8**k+4
    assert numer%7==0 and numer//7==value
    if n>=3: assert value==8*a[n-2]-4
    a.append(value)
    # Identité des coefficients après multiplication par (1-x)(1-8x²).
    lhs=value-a[n-1]-(8*a[n-2] if n>=2 else 0)+(8*a[n-3] if n>=3 else 0)
    assert lhs=={1:1,2:1,3:-6}.get(n,0)
for row in rows:
    n=int(row['n']); assert int(row['complement_riordan'])==a[n]
print('Formes fermées, récurrence et identité génératrice : contrôles exacts n=1..1000 réussis.')
(root/'formes_chatgpt.txt').write_text('Contrôles exacts n=1..1000 réussis : somme, formes par parité, récurrence et identité génératrice.\n')
