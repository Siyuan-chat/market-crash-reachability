"""Static acceptance audit of the V14 analytical manuscript."""
from pathlib import Path
from fractions import Fraction
from decimal import Decimal, getcontext
import re
ROOT=Path(__file__).resolve().parents[1]
OLD=ROOT/"submission/v13-review-response/main.tex"
NEW=ROOT/"submission/v14-turnover-dissipation/main.tex"

def result_blocks(src):
    out=[]
    for env in ("assumption","definition","theorem","proposition","lemma"):
        out.extend((env,m.group()) for m in re.finditer(
            rf"\\begin\{{{env}\}}(?:\[[^\]]*\])?[\s\S]*?\\end\{{{env}\}}",src))
    return sorted(out)

def numbered_equations(src):
    return re.findall(r"\\begin\{equation\}[\s\S]*?\\end\{equation\}",src)

def main():
    old=OLD.read_text(encoding="utf-8")
    new=NEW.read_text(encoding="utf-8")
    old_results=result_blocks(old)
    new_results=result_blocks(new)
    extras=[item for item in new_results if item not in old_results]
    missing=[item for item in old_results if item not in new_results]
    assert not missing, ("Historical statements changed",missing)
    assert len(extras)==1 and extras[0][0]=="proposition", ("Unexpected new results", extras)
    assert r"\label{prop:turnover-dissipation}" in extras[0][1]
    old_eq=numbered_equations(old)
    new_eq=numbered_equations(new)
    assert all(eq in new_eq for eq in old_eq), "Historical numbered equations changed"
    extra_eq=[eq for eq in new_eq if eq not in old_eq]
    assert len(extra_eq)==2, ("Unexpected added numbered equations",len(extra_eq))
    assert any(r"\label{eq:V2-identity}" in eq for eq in extra_eq)
    assert any(r"\label{eq:V2-turnover}" in eq for eq in extra_eq)
    assert len(new_results)==len(old_results)+1
    assert len(new_eq)==len(old_eq)+2
    assert set(re.findall(r"\\label\{([^}]+)\}",old)) <= set(re.findall(r"\\label\{([^}]+)\}",new))
    assert new.count(r"\begin{proof}") == old.count(r"\begin{proof}")+1
    assert new.count(r"\end{proof}") == old.count(r"\end{proof}")+1
    for term in ("Turnover--dissipation bound under constant impact",
                 "Two-session rolling-band example",
                 r"\sum_i|\dot X_i|\le2\sum_e\dot z_e",
                 r"\mathrm e=\exp(1)",
                 r"M(T)\ge0.5382",
                 "cannot become positive",
                 r"\dot M\le NU_{\max}\bar v/2"):
        assert term in new, ("Missing proof/result",term)
    assert r"\sum_i|\dot X_i|=2\sum_e\dot z_e" not in new
    block=new.split(r"\paragraph{Turnover and quadratic dissipation}",1)[1].split(
        r"\section{Finite trading rates and abstract price bands}",1)[0]
    assert r"q_i(t)=\dot X_i(t)" not in block
    assert "compensating assets can make" not in block

    assert r"1.02020225507905<h<1.02020225507908" in new, "Correct interval missing"
    assert "1.020225507905" not in new, "Incorrect left endpoint reappeared"
    f = lambda z: 101600000000*z*z - 97138000000*z - 6646157699
    getcontext().prec=60
    assert f(Decimal("1.02020225507905")) < 0 < f(Decimal("1.02020225507908"))
    assert "the hypothetical original-budget targets" not in new
    assert "failure to find a control by numerical optimization" not in new
    assert "This unpublished research draft" not in new
    bib=(NEW.parent/"references.bib").read_text()
    for title in ("Crossover from linear to square-root market impact",
                  "Fire sales, indirect contagion and systemic stress testing",
                  "The flash crash: high-frequency trading in an electronic market"):
        assert title in bib, ("Bibliography case",title)
    keys=re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,",bib)
    assert len(set(keys))==len(keys)
    cited=set()
    for c in re.findall(r"\\cite[pt]?\s*\{([^}]+)\}",new):
        cited.update(x.strip() for x in c.split(","))
    assert cited <= set(keys), ("Unresolved bib keys",cited-set(keys))
    a=Fraction(3,4)**2
    b=max(Fraction(1)-a,Fraction(5,4)**2-Fraction(1))
    assert a==b==Fraction(9,16)
    d=Fraction(1,50)
    deficit=Fraction(10,2)*(2*d-d*d)
    assert deficit==Fraction(99,500)
    getcontext().prec=35
    Mmin=Decimal(99)/Decimal(500)*Decimal(1).exp()
    assert Decimal("0.5382")<Mmin<Decimal("0.5383")<Decimal(3)

    # Continuous-exponent discussion is unnumbered and does not revise V13/V14 theorems.
    assert new.count(r"\paragraph{The continuous power-law spectrum}") == 1
    spectrum=new.split(r"\paragraph{The continuous power-law spectrum}",1)[1].split(
        r"\paragraph{A concrete common-budget comparison}",1)[0]
    for text in (
        r"0\le p\le2",
        r"E_p(0^+)=F^2/[\eta(1-p)(2-p)]",
        r"e^{-\rho T}<2-p",
        r"T>-\log(2-p)/\rho",
        r"\frac{\eta H_0}{F}",
        "beyond the proven $p=0$ case",
        r"\ref{thm:barrier1}",
        r"\ref{thm:barrier2}",
        r"\ref{prop:three-pulse}",
        r"\ref{prop:two-pulse}",
    ):
        assert text in spectrum, ("Missing exponent regime qualification",text)

    # Independent numerical quadrature sanity checks of the elementary potential.
    import math
    for p in (0.0, 0.25, 0.75, 1.0, 1.25, 1.75, 1.95):
        L=1.2
        if p == 1.0:
            analytic=L+math.exp(-L)-1.0
        else:
            analytic=math.expm1((p-1.0)*L)/(p-1.0) + math.expm1(-(2.0-p)*L)/(2.0-p)
        low=math.exp(-L)
        step=(1-low)/600.0
        def integrand(x):
            return (1.0-x)*x**(-p)
        quadrature=(step/3.0)*(integrand(low)+integrand(1.0)+
            sum((4.0 if j%2 else 2.0)*integrand(low+j*step) for j in range(1,600)))
        assert math.isclose(analytic,quadrature,rel_tol=5e-9,abs_tol=5e-10), (p,analytic,quadrature)
    for p in (0.0,0.5,0.75):
        finite=1/((1-p)*(2-p))
        assert finite>0
        L=60.0
        value=math.expm1((p-1)*L)/(p-1)+math.expm1(-(2-p)*L)/(2-p)
        assert 0 < value <= finite and abs(value-finite)/finite < 1e-5
    for p in (1.25,1.75):
        L=2.0
        E=math.expm1((p-1)*L)/(p-1)+math.expm1(-(2-p)*L)/(2-p)
        bound=math.log1p((p-1)*(E+1/(2-p)))/(p-1)
        assert L <= bound + 1e-12
    print("PASS continuous exponent potentials, finite boundary limits and inventory cap")
    print("PASS V13 theorem/equation/label preservation, citations, exact endpoint arithmetic")
    print("PASS all-asset necessary M>=",Mmin,"(original budget remains inconclusive)")
if __name__=="__main__":
    main()
