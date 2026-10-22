"""Independent squared-price (w=y^2) interval audit of the V16 limit-down path.

Proof coordinate and recurrence differ from the primary y-coordinate checker.
Uses exact rationals for root/knots, integer outward rounding for the w flow,
and integer-square-root brackets; no floating point enters any acceptance test.

The independent certificate proves the same continuous bands, pairing
resources and a *strictly larger than 16.04%* geometric-index loss, rather
than relying on an ordinary numerical RK4 reconstruction. It is a separately
implemented internal audit, not independent third-party verification.
"""
if not __debug__:
    raise RuntimeError("Independent rigorous interval audit rejects python -O")

import argparse
import json
from fractions import Fraction as Fr
from math import isqrt
from pathlib import Path

SCALE = 10**23
STEP = Fr(1, 2000)
assert SCALE % 2000 == 0
STEP_SCALED = SCALE // 2000
RHO = Fr(2, 5)
HLOW = Fr("1.15451858960596")
HHIGH = Fr("1.15451858960597")
TIMES = [Fr(0), Fr(5, 2), Fr(35, 2), Fr(20), Fr(24), Fr(36), Fr(40)]
KNOTS = [
    (Fr(1), Fr(1)), (HLOW, HHIGH), (HLOW, HHIGH),
    (Fr(3, 4), Fr(3, 4)), (Fr(187, 200), Fr(187, 200)),
    (Fr(187, 200), Fr(187, 200)), (Fr(9, 16), Fr(9, 16))
]

def down(n, d):
    return n // d

def up(n, d):
    return -((-n) // d)

class Range:
    """Outward-rounded interval in units of SCALE."""
    __slots__ = ("lo", "hi")
    def __init__(self, lo, hi=None):
        self.lo = int(lo)
        self.hi = int(lo if hi is None else hi)
        assert self.lo <= self.hi

    @staticmethod
    def fraction(lo, hi=None):
        a = Fr(lo)
        b = Fr(lo if hi is None else hi)
        return Range(down(a.numerator * SCALE, a.denominator),
                     up(b.numerator * SCALE, b.denominator))

    def __add__(self, other):
        x = to_range(other)
        return Range(self.lo + x.lo, self.hi + x.hi)
    __radd__ = __add__

    def __neg__(self):
        return Range(-self.hi, -self.lo)

    def __sub__(self, other):
        return self + (-to_range(other))

    def __rsub__(self, other):
        return to_range(other) + (-self)

    def __mul__(self, other):
        x = to_range(other)
        values = (self.lo*x.lo, self.lo*x.hi, self.hi*x.lo, self.hi*x.hi)
        return Range(down(min(values), SCALE), up(max(values), SCALE))
    __rmul__ = __mul__

    def inverse(self):
        assert self.lo > 0
        return Range(down(SCALE*SCALE, self.hi),
                     up(SCALE*SCALE, self.lo))

    def __truediv__(self, other):
        return self * to_range(other).inverse()

def to_range(value):
    return value if isinstance(value, Range) else Range.fraction(value)

def ledger(h):
    """Independent exact evaluation of the six-stage target dollar ledger."""
    xx = [Fr(1), h, h, Fr(3, 4), Fr(187, 200),
          Fr(187, 200), Fr(9, 16)]
    recovery = sum((TIMES[j+1]-TIMES[j]) *
                   ((xx[j]**2+xx[j]*xx[j+1]+xx[j+1]**2)/3 -
                    (xx[j]+xx[j+1])/2) for j in range(6))
    return (xx[-1]**2-1)/2 + RHO*recovery

def verify_plateau():
    c = ledger(Fr(0))
    a = (ledger(Fr(2))-2*ledger(Fr(1))+c)/2
    b = ledger(Fr(1))-a-c
    assert (a, b, c) == (
        Fr(20, 3), Fr(-77, 12), Fr(-2364683, 1600000))
    assert 4800000 * a == 32000000
    assert 4800000 * b == -30800000
    assert 4800000 * c == -7094049
    assert ledger(HLOW) < 0 < ledger(HHIGH)
    assert 2*a*HLOW+b > 0

def audit():
    verify_plateau()
    step = STEP_SCALED
    # For y in (0.7,1.55), w=y^2 remains in (0.49,2.4025).
    # w' = -(4/5)(w-sqrt(w))-2u; f_w=-4/5+(2/5)/sqrt(w)<0,
    # while 1+STEP*f_w>0. Each Euler map is order preserving.
    # Segmentwise exact checks |u|<1/2 and |u'|<1/5 imply
    # |w'| < (4/5)(7/8)+1 = 17/10 < 2;
    # |f_w|<11/20 and |w''|< (11/20)(17/10)+2/5 <2.
    # Taylor remainder per Euler step is < STEP^2.
    err = down(step*step, SCALE)+1
    lower = upper = SCALE
    first_close = None
    terminal_rows = []
    global_rate = 0
    target_sales = comp_sales = total_dollar = 0
    step_count = 0
    all_day_bounds = []
    for j, (start, stop) in enumerate(zip(TIMES[:-1], TIMES[1:])):
        x0 = Range.fraction(*KNOTS[j])
        x1 = Range.fraction(*KNOTS[j+1])
        speed = (x1-x0)/Range.fraction(stop-start)
        stage_x = Range(min(x0.lo, x1.lo), max(x0.hi, x1.hi))
        whole_u = stage_x*(speed+Range.fraction(RHO)*(stage_x-1))
        whole_up = speed*(speed+Range.fraction(RHO)*(2*stage_x-1))
        assert max(abs(whole_u.lo), abs(whole_u.hi)) < SCALE//2
        assert max(abs(whole_up.lo), abs(whole_up.hi)) < SCALE//5
        count = (stop-start)/STEP
        assert count.denominator == 1
        count = int(count)
        step_count += count
        lower_stage = 10*SCALE
        upper_stage = 0
        for n in range(count):
            assert lower > Range.fraction(Fr(7, 10)**2).hi
            assert upper < Range.fraction(Fr(31, 20)**2).lo
            p = x0+speed*Range(n*step)
            q = x0+speed*Range((n+1)*step)
            intrastep_x = Range(min(p.lo,q.lo),max(p.hi,q.hi))
            u = intrastep_x*(speed+Range.fraction(RHO)*(intrastep_x-1))
            # Integer square roots independently bound sqrt(w)*SCALE.
            sqrt_l = isqrt(lower*SCALE)
            root_h = isqrt(upper*SCALE)
            sqrt_h = root_h + (root_h*root_h < upper*SCALE)
            f_lo = down(-4*(lower-sqrt_l), 5)-2*u.hi
            f_hi = up(-4*(upper-sqrt_h), 5)-2*u.lo
            new_lower = lower+down(f_lo*step,SCALE)-err
            new_upper = upper+up(f_hi*step,SCALE)+err
            assert new_lower <= new_upper
            # Bootstrap within step using |w'|<2 on the verified strip.
            inside_lower = min(lower,new_lower)-2*step
            inside_upper = max(upper,new_upper)+2*step
            assert inside_lower > Range.fraction(Fr(7, 10)**2).hi
            assert inside_upper < Range.fraction(Fr(31, 20)**2).lo
            lower_stage = min(lower_stage,inside_lower)
            upper_stage = max(upper_stage,inside_upper)
            x_floor = intrastep_x.lo
            y_floor = isqrt(inside_lower*SCALE)
            assert x_floor > 0 and y_floor > 0
            umax = max(abs(u.lo),abs(u.hi))
            global_rate = max(global_rate,up(umax*SCALE,x_floor),
                              up(umax*SCALE,y_floor))
            target_sales += up(max(0,-u.lo)*step,x_floor)
            comp_sales += up(max(0,u.hi)*step,y_floor)
            total_dollar += up(5*umax*step,SCALE)
            lower,upper = new_lower,new_upper

        # First day: w in [(3/4)^2, (5/4)^2].
        if stop <= 20:
            assert lower_stage > Range.fraction(Fr(3,4)**2).hi
            assert upper_stage < Range.fraction(Fr(5,4)**2).lo
        else:
            # Second day: w in [(3/4)^2*w(20), (5/4)^2*w(20)].
            assert first_close is not None
            assert lower_stage > up(9*first_close[1],16)
            assert upper_stage < down(25*first_close[0],16)

        if stop == 20:
            first_close = (lower,upper)
        terminal_rows.append({
            "time": str(stop),
            "w_at_close": [str(Fr(lower,SCALE)),str(Fr(upper,SCALE))],
            "w_within_segment": [str(Fr(lower_stage,SCALE)),
                                 str(Fr(upper_stage,SCALE))]
        })
        all_day_bounds.append((lower_stage,upper_stage))

    assert step_count == 80000
    assert global_rate < Fr("0.285")*SCALE
    assert target_sales < 2*SCALE
    assert comp_sales < 2*SCALE
    assert total_dollar < 14*SCALE

    # To certify G=(x^5*y^5)^(1/10)=sqrt(x*y) < 0.8396,
    # it is equivalent to w=y^2 < ((0.8396)^2/(9/16))^2.
    index_bound = Fr("0.8396")
    terminal_w_threshold = (index_bound**2/Fr(9,16))**2
    assert Fr(upper,SCALE) < terminal_w_threshold
    assert upper < Fr("1.253")**2*SCALE

    result = {
        "status": "separately implemented internal validated interval audit",
        "method": "squared-price w=y^2 with integer-square-root bounds and monotone Euler map",
        "independent_of_primary_y_variable_checker": True,
        "steps": step_count,
        "scale": str(SCALE),
        "step": str(STEP),
        "terminal_w_enclosure": [str(Fr(lower,SCALE)),str(Fr(upper,SCALE))],
        "terminal_y_strict_upper": "1.253",
        "certified_geometric_index_ratio_strict_upper": "0.8396",
        "certified_geometric_index_decline_strict_lower": "0.1604",
        "per_asset_gross_share_rate_upper": str(Fr(global_rate,SCALE)),
        "target_sales_upper": str(Fr(target_sales,SCALE)),
        "compensator_sales_upper": str(Fr(comp_sales,SCALE)),
        "matched_dollar_turnover_upper": str(Fr(total_dollar,SCALE)),
        "stages": terminal_rows,
        "scope": "No external third-party proof-code audit is claimed"
    }
    return result

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--out",default=None)
    args = parser.parse_args()
    result = audit()
    print("PASS independent w=y^2 validated 80,000-step interval enclosure")
    print("PASS both daily bands, per-asset rates/inventory, exact plateau root")
    print("PASS strict geometric-index ordinary decline >16.04 percent")
    print("PASS", "terminal w interval:",result["terminal_w_enclosure"])
    print("PASS", "rate:",result["per_asset_gross_share_rate_upper"],
          "turnover:",result["matched_dollar_turnover_upper"])
    if args.out:
        Path(args.out).parent.mkdir(parents=True,exist_ok=True)
        Path(args.out).write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")

if __name__=="__main__":
    main()
