#!/usr/bin/env python3
"""Exact rational checks for the V20 two-day gross-share rate bracket.

Does not numerically solve a market ODE and is not a verifier for the
analytic continuous-dependence theorem above p=3/2.
"""
from fractions import Fraction as Q

a, b = Q(1, 8), Q(1, 2)
# For t in [0,1/2], the alternating geometric truncation gives
# 1/(1+t^2) >= 1-t^2+t^4-t^6.
lower_integral = sum(
    (-1)**j * (b**(2*j+1)-a**(2*j+1))/Q(2*j+1)
    for j in range(4)
)
assert lower_integral == Q(24890949,73400320)
assert lower_integral > Q(169,500)
assert lower_integral/20 > Q(169,10000)
assert Q(169,10000) < Q(133,1000)
# The shape of the scalar potential follows from p=0, K=2:
# d/dx atan(2*x-1) = 1/(1+2*x*(x-1)).
assert Q(1)+2*Q(3,4)*(Q(3,4)-1)>0
assert Q(1)+2*Q(9,16)*(Q(9,16)-1)>0
print("PASS: positive lower five-target gross share-rate bound > 0.0169")
print("PASS: lower bound < certified strict upper witness bound 0.133")
print("SCOPE: arithmetic only; no proof of the sharp rate or full coverage k*")
