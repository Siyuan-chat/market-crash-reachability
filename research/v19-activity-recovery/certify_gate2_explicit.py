#!/usr/bin/env python3
"""Exact-rational checks for explicit positive-h Gate 2 constructions I and II.

Checks numerical inequalities, not the analytic Banach/IVT argument.
Does NOT certify the legacy h=.2 or h=.012 numerical witnesses.
"""
from fractions import Fraction as Q
from math import factorial
h=Q(1,10**16); r=Q(1,10**6); a0=10**17
assert Q(3162,1000)**2<10<Q(3163,1000)**2
assert sum(Q(16)**k/factorial(k) for k in range(12))>100000
# I: rho=2/5, T=40, b in [3/50,7/100].
rho=Q(2,5); bl=Q(3,50); bu=Q(7,100)
Hl=1-9*bu**2+9*bu
Hu=1-Q(9,2)*bl**2+9*bl
El=(1-Q(1,100000))*Hl/Q(3163,1000)-Q(1,2)
Eu=Q(1,100000)+Hu/Q(3162,1000)-Q(1,2)
assert El>Q(1,1000) and Eu<Q(-1,100)
z=1+9*bl*(1-9*bu**2-bu)
assert z*(z-1)>Q(7,10)
assert Q(40)*Q(7,10)/(10*13)>Q(1,5)
inv=Q(25,2)/(rho*Q(7,10))
assert inv<45
assert 4*18+rho*40*9*18+rho*2*12*11<2800
derr=rho*(2*9*(18+2)+9*4)+rho*9*(2*rho*4)+4*rho*rho*4
assert derr<200
assert inv*(rho*4*100*r+9*2*200*h)<Q(1,4)
assert inv*(2*2800*h)<r/2
assert a0>5/h+8
assert Q(10*a0*40,2)==2*10**19
assert a0*40/bl<10**20
# II: rho=1, T=200, c=1/100, b in [1e-5,1/20], q<=1/100.
c=Q(1,100);bl=Q(1,100000);bu=Q(1,20);q0=Q(1,100)
amin=1-8*c*c-bu*bu
assert amin>Q(996,1000)
Hlo=1-8*c*c-bl*bl+8*c+bl
assert Hlo>Q(1079,1000)
assert 1+8*c+bu<Q(3,2)
Fl=(Q(1079,1000)**2-1)/2-200*bl*4-Q(9*10,2)*q0*q0
Fu=Q(9,2)-200*bu*(1-4*bu)
assert Fl>Q(6,100) and Fu<-3
z=1+8*c*(amin-c)
assert z*(z-1)>Q(8,100)
assert 200*Q(8,100)/(9*13)>Q(13,100)
inv=Q(10)/Q(8,100)
assert inv==125
assert 4*40+200*9*40+2*12*10==72400
assert 2*9*(40+4)+9*8+9*(2*4)+4*4<1000
assert inv*(4*100*r+8*2*1000*h)<Q(1,4)
assert inv*(2*72400*h)<r/2
assert a0>5/h+20
assert Q(10*a0*200,2)==10**20
assert a0*(Q(200)/bl+2*h/c)<3*10**24
print("PASS: exact-rational sharp endpoints, stage gaps,")
print("       fixed-h contraction bounds and uniform C0 resource envelopes")
print("Scope: analytic alternative witnesses, NOT cached numerical roots")
