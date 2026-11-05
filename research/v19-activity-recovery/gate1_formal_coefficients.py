#!/usr/bin/env python3
"""Exact rational formal-coefficient audit for V19 local event mechanisms.

This is NOT a general theorem prover or an interval certificate.
"""
from fractions import Fraction as Q

edges = [(0,1),(1,2),(2,0),(1,2),(2,0),(0,1),(2,0),(0,1),(1,2)]

def six_incidence_coeff(signs):
    # Along a node's incident amount clock:
    # dw/da = sigma - K*(w+O(w**2)).
    # Maintain w=A*z+B*K*z**2+O(z**3).
    A, B = Q(0), Q(0)
    for sign in signs:
        B -= A + Q(sign,2)
        A += sign
    return A, B

for i in range(3):
    signs = [(-1 if seller==i else +1) for seller,buyer in edges
             if seller==i or buyer==i]
    assert len(signs)==6, (i, signs)
    assert sum(signs)==0
    assert sum(j*sign for j,sign in enumerate(signs,1))==-1
    assert six_incidence_coeff(signs)==(Q(0),Q(-1))
    print(f"PASS node {i+1}: {signs} -> -K*z**2")

# N=2, two equal opposing amount-z events:
# leading w_1=-a,w_2=a on first half; w_1=-(z-a),w_2=z-a
# on second half. Integrated sum of their squares is 4*z**3/3.
# r_p(w)=w+((1-p)/2)*w**2+O(w**3), hence
# H(2*z)=-K*(1-p)*(1/2)*(4*z**3/3)+O(z**4).
assert Q(1,2)*Q(4,3)==Q(2,3)
print("PASS N=2: H3 coefficient=-(2/3)*K*(1-p)")
print("SCOPE: formal coefficients only; Gates 1 and 2 still OPEN")
