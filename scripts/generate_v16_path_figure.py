"""Generate an auditable TikZ path/rate figure from V16's exact control knots.

The plot is a numerical *visualization* (RK4), not a proof. The captions
identify this; the interval certificates independently guarantee bands,
positive prices and resources. No image generator or artist interpolation.
"""
from pathlib import Path
import argparse
import math

RHO=0.4
TIMES=[0,2.5,17.5,20,24,36,40]
A=32000000.0; B=-30800000.0; C=-7094049.0
H=(-B+math.sqrt(B*B-4*A*C))/(2*A)
TARGET=[1,H,H,.75,.935,.935,.5625]

def simulate():
    rows=[]
    y=1.0
    for seg,(a,b) in enumerate(zip(TIMES[:-1],TIMES[1:])):
        slope=(TARGET[seg+1]-TARGET[seg])/(b-a)
        steps=round((b-a)*100)
        assert abs(steps/100-(b-a))<1e-9
        dt=(b-a)/steps
        def rhs(t, yy):
            x=TARGET[seg]+slope*(t-a)
            u=x*(slope+RHO*(x-1))
            return -RHO*(yy-1)-u/yy
        segment=[]
        for j in range(steps+1):
            t=a+j*dt
            x=TARGET[seg]+slope*(t-a)
            u=x*(slope+RHO*(x-1))
            if j==0 or j==steps or j%20==0:
                segment.append((t,x,y,abs(u)/x,abs(u)/y))
            if j<steps:
                k1=rhs(t,y)
                k2=rhs(t+dt/2,y+dt*k1/2)
                k3=rhs(t+dt/2,y+dt*k2/2)
                k4=rhs(t+dt,y+dt*k3)
                y+=dt*(k1+2*k2+2*k3+k4)/6
        rows.append(segment)
    assert abs(rows[2][-1][2]-1.178153)<0.002
    assert abs(y-1.252494)<0.002
    assert all(p[2]>0 for segment in rows for p in segment)
    return rows

def coordinates(rows,idx,group=False):
    pointsets=rows if group else [[p for seg in rows for p in seg]]
    return "\n".join(
        "  \\draw["+("teal!70!black" if idx in (1,3) else "magenta!85!black")+
        ",thick] plot coordinates {"+
        " ".join(f"({p[0]:.3f},{p[idx]:.7f})" for p in seg)+
        "};" for seg in pointsets)

def generate():
    r=simulate()
    return (
r"""\begin{figure}[!t]
\centering
\resizebox{0.98\linewidth}{!}{%
\begin{tikzpicture}[font=\scriptsize,>=stealth]
% Panel (a): exact target knots and numerically reconstructed compensator ODE.
\begin{scope}[shift={(0,-1.395cm)},x=.14cm,y=3.1cm]
\draw[->] (0,0.45)--(42,0.45) node[right] {$t$};
\draw[->] (0,0.45)--(0,1.42) node[above] {$S_i$};
\draw[dashed,gray] (0,1)--(40,1) node[right] {$F$};
\draw[densely dashed,gray!60] (20,0.45)--(20,1.40);
\foreach \t in {0,20,40}{\draw (\t,0.45)--(\t,0.42) node[below] {\t};}
\foreach \p in {0.5,0.75,1,1.25}{\draw (0,\p)--(-.4,\p) node[left] {\p};}
\node[anchor=west] at (0,1.58) {\textbf{(a) Price trajectories}};
""" + coordinates(r,1) + "\n" +coordinates(r,2)+r"""
\fill[teal!70!black] (20,.75) circle (.020);
\fill[teal!70!black] (40,.5625) circle (.020);
\node[teal!70!black,anchor=west] at (2,1.48) {Five targets $x(t)$};
\node[magenta!85!black,anchor=west] at (23,1.48) {Five compensators $y(t)$};
\end{scope}
% Panel (b): absolute gross share rates before netting.
\begin{scope}[shift={(7.2cm,0)},x=.14cm,y=8.6cm]
\draw[->] (0,0)--(42,0) node[right] {$t$};
\draw[->] (0,0)--(0,.34) node[above] {Gross rate};
\draw[dashed,gray] (0,.285)--(40,.285);
\draw[densely dashed,gray!60] (20,0)--(20,.32);
\foreach \t in {0,20,40}{\draw (\t,0)--(\t,-.009) node[below] {\t};}
\foreach \p in {0,.15,.285}{\draw (0,\p)--(-.4,\p) node[left] {\p};}
\node[anchor=west] at (0,.407) {\textbf{(b) Gross share execution rates}};
""" + coordinates(r,3,True) + "\n" + coordinates(r,4,True) +r"""
\node[teal!70!black,anchor=west] at (2,.370) {Targets $|u|/x$};
\node[magenta!85!black,anchor=west] at (23,.370) {Compensators $|u|/y$};
\end{scope}
\end{tikzpicture}%
}
\caption{\textbf{Consecutive lower-limit construction under a common rolling band.}
Numerical reconstruction of the fixed-control path in Proposition~\ref{prop:five-two-day-limits}.
Five target assets have identical prices $x(t)$, close at $0.75F$ on the first session
and $0.5625F$ on the second, while five compensators follow the scalar ODE for $y(t)$.
The two asset groups are paired dollar-for-dollar, and their gross share rates
remain below $0.285$ per asset. Trajectory curves are numerical visualization
only; exact ledger closure and pathwise admissibility are established by the
analytical construction and outward-rounded interval certificates.}
\label{fig:two-day-price-rate}
\end{figure}
""")

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--out",required=True)
    args=parser.parse_args()
    out=Path(args.out)
    out.parent.mkdir(parents=True,exist_ok=True)
    content=generate()
    out.write_text(content,encoding="utf-8")
    assert "fig:two-day-price-rate" in content
    print("PASS reproducible V16 two-panel TikZ price/rate visualization:",out)

if __name__=="__main__":
    main()
