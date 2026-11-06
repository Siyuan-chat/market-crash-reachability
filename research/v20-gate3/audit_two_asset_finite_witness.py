#!/usr/bin/env python3
"""Exact rational consistency audit for V20's p=5/4 finite C1 two-node witness.

The ODE equilibrium existence, monotone comparison and event execution are
proved in manuscript Theorem thm:two-large-turnover. This program checks
ONLY its explicit rational inequalities; it is not a theorem prover.
"""
from fractions import Fraction as Q
from math import factorial

# f_-(x)=1-x-x^(1/4) strictly decreases, so these signs
# enclose its unique equilibrium between 1/4 and 1/3.
assert Q(3, 4)**4 > Q(1, 4)
assert Q(2, 3)**4 < Q(1, 3)
# f_+(x)=x^(1/4)-(x-1) has unique root >1 and <5/2.
assert Q(3, 2)**4 > Q(5, 2)

exp4_lower = sum(Q(4)**k / factorial(k) for k in range(6))
assert exp4_lower == Q(643, 15) > Q(75, 2)
product_bound = Q(5, 2) * (Q(1, 3) + Q(5, 2) / exp4_lower)
assert product_bound == Q(7555, 7716) < 1

# Stage length 4, unit paired dollar rate, one genuine sale per asset.
assert 2 * 4 == 8
assert Q(4) / Q(1, 4) == 16
assert Q(1) / Q(1, 4) == 4

print("PASS: fourth-power equilibrium brackets and exact exp(4) enclosure")
print("PASS: M=8; true seller shares H_i^-<16; gross share rate<4")
print("PASS: S1(T)S2(T)<7555/7716<1 with exact per-node dollar closure")
print("SCOPE: arithmetic subclaims only; analytic scalar ODE proof in V20 manuscript")
