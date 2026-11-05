#!/usr/bin/env python3
"""Independent small analytical-regression tests, no old time-decay model."""
import math,unittest
from fractions import Fraction as Q

EDGES=((0,1),(1,2),(2,0),(1,2),(2,0),(0,1),(2,0),(0,1),(1,2))

def rk4_step(s,h,ds):
    a=ds(s)
    b=ds(s+h*a/2)
    c=ds(s+h*b/2)
    d=ds(s+h*c)
    return s+h*(a+2*b+2*c+d)/6

def one_edge(x,sgn,z,p,k):
    # dx/da = sgn*x^(p-1)-k*(x-1), in normalized dollar activity
    n=100
    h=z/n
    for _ in range(n):
        x=rk4_step(x,h,lambda y:sgn*y**(p-1)-k*(y-1))
        assert x>0
    return x

class CheckActivity(unittest.TestCase):
    def test_zero_activity_is_stationary(self):
        self.assertEqual(one_edge(1.3,0,0,p=0,k=2),1.3)
    def test_ledger_closes_nine_edge_protocol(self):
        net=[0.,0.,0.]
        for i,j in EDGES:net[i]-=.001;net[j]+=.001
        self.assertLess(max(map(abs,net)),1e-15)
    def test_triangle_quadratic(self):
        z=.0006;k=.8
        for p in (0,1,2):
            prices=[1.]*3
            for i,j in EDGES:
                prices[i]=one_edge(prices[i],-1,z,p,k)
                prices[j]=one_edge(prices[j],+1,z,p,k)
            for val in prices:
                self.assertLess(val,1)
                self.assertAlmostEqual((1-val)/(k*z*z),1,delta=.008)
    def test_floor_constant_impact(self):
        k=5.;floor=(1+math.sqrt(1-4/k))/2
        x=1.
        for _ in range(1000):x=one_edge(x,-1,.003,0,k)
        self.assertGreater(x,floor-1e-9)
    def test_K_critical(self):
        self.assertEqual((2-0)**(2-0)/(1-0)**(1-0),4)
        self.assertGreater((2-.5)**(2-.5)/(1-.5)**(1-.5),1)
    def test_primitive_derivative(self):
        import mpmath as m
        m.mp.dps=40
        def P(x,sgn):
            v=x-m.mpf('.5')
            if sgn==1:
                return -m.log(m.mpf('1.5')-2*v*v)/4+m.atanh(2*v/m.sqrt(3))/(2*m.sqrt(3))
            return m.log(2*v*v+m.mpf('.5'))/4+m.atan(2*v)/2
        for sgn in (-1,1):
            for x in (m.mpf('.75'),m.mpf('1.0'),m.mpf('1.25')):
                deriv=m.diff(lambda y:P(y,sgn),x)
                self.assertLess(abs(deriv-x/(1-sgn*2*x*(x-1))),m.mpf('1e-28'))

if __name__=='__main__':unittest.main()
