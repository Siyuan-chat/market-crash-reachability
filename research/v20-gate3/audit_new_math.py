#!/usr/bin/env python3
"""Exact rational QA for selected NEW Gate 3 algebra, not theorem automation.

This script checks finite-dimensional coefficients and elementary sufficient
inequalities. It cannot prove all assumptions of the manuscript, ODE
existence, or Gate 3 completeness.
"""
from fractions import Fraction as F
from math import factorial

def two_event_terminal_log_z2(kappa: F, D: F, sigma: int) -> F:
    """Return the second-order Taylor coefficient after +-sigma edge events.

    For quadratic response x'= (sigma/D-kappa)*x + kappa on each edge,
    composing two z-length edge flows from x=1 gives x(2z)=1+coef*z²+O(z³).
    Since the linear term is zero, log x has the same z² coefficient.
    """
    u = F(sigma, 1) / D
    a1, a2 = u - kappa, -u - kappa
    first = (a1 * u) / 2
    second = a2 * u + a2 * (a2 + kappa) / 2
    assert u + (a2 + kappa) == 0
    return first + second

for kappa, D, sigma in [(F(2), F(1), 1),
                         (F(1), F(1), -1),
                         (F(17, 9), F(3, 2), 1),
                         (F(1, 20), F(27, 11), -1)]:
    assert two_event_terminal_log_z2(kappa, D, sigma) == -sigma*kappa/D

k1, D1, k2, D2 = F(2), F(1), F(1), F(1)
q1 = two_event_terminal_log_z2(k1, D1, +1)
q2 = two_event_terminal_log_z2(k2, D2, -1)
assert (q1, q2) == (-2, 1)
assert -(q1+q2)/2 == F(1, 2) > 0  # mean-log-loss coefficient

# Elementary rational certificates for the analytic delta ladder:
# e^5 > 100, so q=exp(-2*delta-5) < 0.01 for delta >= 0.
assert sum((F(5)**n)/factorial(n) for n in range(7)) > 100
# exp(2)>4 -> log 4 < 2. Then L_target > 2*delta+3;
# L_comp > -2; average loss > [9*(2*delta+3)-2]/10.
assert sum((F(2)**n)/factorial(n) for n in range(3)) > 4
for delta in [3, 5, 10, 20]:
    target_bound = 2*delta + 3
    average_bound = F(9*target_bound-2, 10)
    assert target_bound > delta and average_bound > delta

# General p<1 integrability of q->0 final affine direction ramp.
for nu in [F(2), F(7, 4), F(5, 4), F(101, 100)]:
    assert nu > 1 and nu/(nu-1) > 0

print('PASS: 2-node quadratic-heterogeneous leading coefficient, exact rationals')
print('PASS: analytic severity ladder delta 3, 5, 10, 20 under fixed M,H envelopes')
print('PASS: terminal-inventory integrability formula for sampled rational nu>1')
print('SCOPE: algebraic regression checks only, not a proof of all mathematical hypotheses')