#!/usr/bin/env python3
"""Exact rational Green-matrix inverse audit for 9 and 10 role stages."""
from fractions import Fraction as F

def audit(m):
    n=m-1
    g=[[F(min(i,j)*(m-max(i,j)),m) for j in range(1,m)]
       for i in range(1,m)]
    for i in range(n):
        for j in range(n):
            z=2*g[i][j]
            if i>0: z-=g[i-1][j]
            if i+1<n: z-=g[i+1][j]
            assert z==(1 if i==j else 0)
    norm=max(sum(row) for row in g)
    assert norm==max(F(i*(m-i),2) for i in range(1,m))
    print(f"PASS: m={m}, exact Green matrix, infinity norm={norm}")
audit(9)
audit(10)
print("SCOPE: exact finite-dimensional identities only; no smooth root certificate")
