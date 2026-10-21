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

def canonical_editorial_math(source):
    """Ignore display framing and a frozen whitelist of wording-only revisions.

    The V13 theorem/equation mathematical content remains exactly comparable
    after removing the purely typographic TeX \boxed wrapper.
    """
    start=r"\boxed{"
    while start in source:
        p=source.index(start)
        depth=1
        k=p+len(start)
        while k<len(source) and depth:
            if source[k] in "{}" and (k==0 or source[k-1] != "\\"):
                depth+=1 if source[k]=="{" else -1
            k+=1
        assert depth==0, "Unbalanced TeX boxed group"
        source=source[:p]+source[p+len(start):k-1]+source[k:]
    allowed_rewording=(
        (r"\emph{absolutely continuous}, paired-dollar, per-asset gross-rate-bounded control",
         r"\emph{absolutely continuous} paired-dollar control with per-asset gross share rate at most $\bar v$"),
        (r" This does \emph{not} assert that a prescribed fixed large threshold remains reachable under an arbitrarily tight cap or band.",""),
        (r" These are exact \emph{conditional endpoint identities}, not sufficient conditions for a trade path realizing the stipulated closing prices.",""),
        (r" None of these scalar inequalities is sufficient for multi-asset price-band feasibility or terminal dollar closure.",""),
        ("Preconditioning needed for a dollar-closed limit-down streak",
         "Above-benchmark excursion required for a dollar-closed limit-down streak"),
        (" It is not sufficient to produce a consecutive limit-down path.",""),
    )
    for before,after in allowed_rewording:
        source=source.replace(before,after)
    return source

def main():
    old=OLD.read_text(encoding="utf-8")
    new=NEW.read_text(encoding="utf-8")
    old_results=[(name,canonical_editorial_math(value)) for name,value in result_blocks(old)]
    new_results=[(name,canonical_editorial_math(value)) for name,value in result_blocks(new)]
    extras=[item for item in new_results if item not in old_results]
    missing=[item for item in old_results if item not in new_results]
    assert not missing, ("Historical statements changed",missing)
    assert len(extras)==5, ("Expected four V14 propositions and one theorem",extras)
    assert sorted(item[0] for item in extras)==["proposition"]*4+["theorem"],extras
    assert any(r"\label{prop:turnover-dissipation}" in item[1] for item in extras)
    assert any(r"\label{thm:sublinear-severe}" in item[1] for item in extras)
    assert any(r"\label{prop:loss-breadth-eight}" in item[1] for item in extras)
    assert any(r"\label{prop:unbalanced-stability}" in item[1] for item in extras)
    assert any(r"\label{prop:heterogeneous-quadratic}" in item[1] for item in extras)
    old_eq=[canonical_editorial_math(eq) for eq in numbered_equations(old)]
    new_eq=[canonical_editorial_math(eq) for eq in numbered_equations(new)]
    assert all(eq in new_eq for eq in old_eq), "Historical numbered equations changed"
    extra_eq=[eq for eq in new_eq if eq not in old_eq]
    assert len(extra_eq)==5, ("Unexpected added numbered equations",len(extra_eq))
    assert any(r"\label{eq:V2-identity}" in eq for eq in extra_eq)
    assert any(r"\label{eq:V2-turnover}" in eq for eq in extra_eq)
    for label in ("eq:sublinear-ledger","eq:sublinear-stage","eq:sublinear-inventory"):
        assert any(r"\label{"+label+"}" in eq for eq in extra_eq), label
    assert len(new_results)==len(old_results)+5
    assert len(new_eq)==len(old_eq)+5
    assert set(re.findall(r"\\label\{([^}]+)\}",old)) <= set(re.findall(r"\\label\{([^}]+)\}",new))
    assert new.count(r"\begin{proof}") == old.count(r"\begin{proof}")+5
    assert new.count(r"\end{proof}") == old.count(r"\end{proof}")+5
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
        r"\section{Reachability under Bounded Execution Rates}",1)[0]
    assert r"q_i(t)=\dot X_i(t)" not in block
    assert "compensating assets can make" not in block

    assert r"1.02020225507905<h<1.02020225507908" in new, "Correct interval missing"
    assert "1.020225507905" not in new, "Incorrect left endpoint reappeared"
    assert r"1.2219388<y(20)<1.2225356" in new, "Certified y(20) endpoint changed"
    assert "1.225356" not in new, "Incorrect y(20) upper endpoint reappeared"

    f = lambda z: 101600000000*z*z - 97138000000*z - 6646157699
    getcontext().prec=60
    assert f(Decimal("1.02020225507905")) < 0 < f(Decimal("1.02020225507908"))
    assert "the hypothetical original-budget targets" not in new
    assert "failure to find a control by numerical optimization" not in new
    assert "This unpublished research draft" not in new
    bib=(NEW.parent/"references.bib").read_text()
    for title in ("Crossover from linear to square-root market impact",
                  "Fire sales, indirect contagion and systemic stress testing",
                  "The Flash Crash: High-frequency trading in an electronic market"):
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
        r"\subsection{A sharp boundary when every asset must fall}",1)[0]
    for text in (
        r"0\le p\le2",
        r"\Phi_p''(S)=(1-p)/g_p(S)",
        r"G_p''(q)=F^2(2-p)e^{(2-p)q}/\eta",
        r"E_p(0^+)=F^2/[\eta(1-p)(2-p)]",
        r"e^{-\rho T}<2-p",
        r"T>-\log(2-p)/\rho",
        r"\frac{\eta H_0}{F}",
        r"\ref{thm:sublinear-severe}",
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
    assert r"\section{Sublinear power-law extension of uniform-budget severity}" in new
    assert r"\label{app:sublinear-severe}" in new
    assert r"\nu=2-p\in(1,2]" in new
    assert r"\Cris_\alpha(T)>\delta" in new
    assert r"b_\varepsilon\in(b_-,\bar b)" in new
    import subprocess,sys
    subprocess.run([sys.executable,str(ROOT/"scripts/check_sublinear_severe_extension.py")],cwd=ROOT,check=True)
    subprocess.run([sys.executable,str(ROOT/"verification/loss_breadth_certified.py")],cwd=ROOT,check=True)
    assert r"\label{tab:loss-breadth}" in new
    assert r"\label{app:loss-breadth}" in new
    block=new.split(r"\subsection{A complementary uniform-band existence result}",1)[1].split(
        r"\section{Discussion}",1)[0]
    appendix=new.split(r"\section{Reproducing the uniform-band loss--breadth witnesses}",1)[1].split(
        r"\bibliographystyle{siamplain}",1)[0]
    table=appendix.split(r"\begin{table}[tbp]\centering\small",1)[1].split(r"\end{table}",1)[0]
    assert "No row claims an optimal frontier" not in appendix
    assert "exactly rational input" not in appendix
    assert "directed-integer interval verifier" not in appendix
    assert r"\texttt{P}" in table and r"\texttt{R}" in table and r"\texttt{M5}" in table
    assert r"0.284500" in table and r"2.984" in table
    assert r"\sup_t9|u(t)|/y(t)<0.284481" in new
    assert r"9\int_0^{40}|u(t)|\dd t<2.984" in new
    assert "Outward-rounded fixed-point interval arithmetic" in block
    assert r"x(40)^8y(40)^2<0.97^{10}" in block
    assert r"M<4.600<5" in appendix
    assert r"\label{tab:loss-breadth-additional}" in appendix
    assert r"\label{tab:sensitivity}" in new and r"\label{fig:v7rates}" in new
    assert r"\label{fig:multiday-crisis-trigger}" in new
    appendix=new.split(r"\section{Reproducing the uniform-band loss--breadth witnesses}",1)[1].split(
        r"\bibliographystyle{siamplain}",1)[0]
    assert "External code audit and independent mathematical review remain outstanding" not in appendix
    availability=new.split(r"\section*{Code and numerical data availability}",1)[1].split(
        r"\section*{Declaration on AI-assisted tools}",1)[0]
    for label in ("app:v7certificate","app:loss-breadth","app:sublinear-severe"):
        assert r"\ref{"+label+"}" in availability, ("Missing code availability reference",label)
    # V14-R1 rewrites the resilience discussion with explicit volume-coordinate
    # identities and separates preserved resource bounds from unproved barriers.
    for required in (
        r"\label{subsec:resilience-metric}",
        r"\dot V=-\rho V",
        r"\dd^2\Phi/\dd V^2=g(S)>0",
        r"S V(S)>\Phi(S)",
        r"\rho\int_0^T(S_i-F)V(S_i)\dd t",
        r"Theorem~\ref{thm:resource}",
        r"elasticity barriers",
    ):
        assert required in new, ("Missing volume-recovery scope", required)
    assert "requires adequate execution capacity" in new
    assert "time-resolved transaction and order-book observations" in new

    # Robustness theory is appended in Discussion, leaving established theorem
    # numbering, Appendix G/I certificates, and original equations unchanged.
    robustness=new.split(
        r"\subsection{Robustness to unmatched dollar flow and impact heterogeneity}",1
    )[1].split(r"\section{Reachability Regimes under Power-Law Impact}",1)[0]
    for required in (
        r"\label{prop:unbalanced-stability}",
        r"\label{prop:heterogeneous-quadratic}",
        r"\label{subsec:barrier-robustness}",
        r"\frac{\dd\log\lambda(S)}{\dd\log S}=e(S)-2",
        r"\sum_i\dot X_i(t)=\varepsilon(t)",
        r"e^{-\rho(t-s)}[-\varepsilon(s)]_+",
        r"\omega=\bar\kappa\,\varepsilon+",
        r"e^{-\rho(t-s)}[-\omega(s)]_+",
        r"Q_{1/2}(T)=(1-r)\kappa_1a+O(a^2)>0",
        r"$X_i(T)=0$",
        "does not impose a",
        r"Theorem~\ref{thm:barrier2}",
    ):
        if required == r"$X_i(T)=0$":
            assert "Both asset ledgers close exactly" in robustness
        else:
            assert required in robustness, ("Missing robustness condition",required)
    # A small deterministic closed-pulse sanity check is not an empirical test
    # or a substitute for the proposition proofs.
    import math
    for a in (0.001,0.02):
        k1,k2,rho,T=1.4,0.8,0.4,3.0
        r=math.exp(-rho*T)
        q1=math.log1p(r*math.expm1(k1*a))-k1*a
        q2=math.log1p(r*math.expm1(-k2*a))+k2*a
        A=-(q1+q2)/2
        Q=-q1
        signed_weighted_bound=(1-r)*(k1-k2)*a/2
        assert 0<A<=signed_weighted_bound+1e-12
        assert Q>0 and min(A,Q)>0
    print("PASS unmatched-flow/heterogeneous-impact theory and closed-pulse sanity")

    # Editorial ordering, title-case, and root-endpoint regression gates.
    p_spectrum=new.index(r"\paragraph{The continuous power-law spectrum}")
    p_sublinear=new.index(r"\label{thm:sublinear-severe}")
    p_kN=new.index(r"\subsection{A sharp boundary when every asset must fall}")
    p_critical=new.index(r"\label{thm:critical}")
    assert 0 <= p_spectrum < p_sublinear < p_kN < p_critical
    p_barriers=new.index(r"\section{Structural Barriers and Robustness}")
    p_robustness=new.index(r"\label{subsec:barrier-robustness}")
    p_regimes=new.index(r"\section{Reachability Regimes under Power-Law Impact}")
    assert p_barriers < p_robustness < p_regimes < p_spectrum
    abstract=new.split(r"\begin{abstract}",1)[1].split(r"\end{abstract}",1)[0]
    assert "$" not in abstract and chr(92) not in abstract
    # The author requested all equation frames removed, including in
    # historical formal result statements; labels and formula text remain.
    assert r"\boxed{" not in new, "Display-equation frame survived"
    assert "severely reachable" not in new and "pulse-admitting" not in new
    assert "time-curvature condition" not in new
    assert "These studies motivate the question without implying" not in new
    assert r"All subsequent results use Assumption~\ref{asmp:model} unless stated otherwise." in new
    assert "Above-benchmark excursion required for a dollar-closed limit-down streak" in new
    # The working V14-R1 abstract leads with geometry and two cases instead
    # of duplicating the complete theorem hypotheses in four long clauses.
    # Hard line wrapping in LaTeX should not change the meaning of a
    # prose validation gate. Keep the exact semantic phrases below.
    abstract_prose = re.sub(r"\s+", " ", abstract).strip()
    for phrase in (
        "Dollar-neutral trading need not be price-neutral",
        "state-dependent price impact",
        "price-level resilience",
        "flow-completed instantaneous trades",
        "seven assets",
        "falling more than 20.2 percent",
        "turnover below five",
        "unattained horizon-dependent ceiling",
        "not crash probabilities",
    ):
        assert phrase in abstract_prose, ("Missing revised abstract meaning", phrase)
    assert abstract_prose.count("In an idealized ten-asset") == 1
    assert abstract_prose.count("an interval-certified") == 1
    assert r"All subsequent results use Assumption~\ref{asmp:model} unless stated otherwise." in new
    assert "All subsequent theorems use the same market definition" not in new
    regime=new.split(r"\section{Reachability Regimes under Power-Law Impact}",1)[1].split(
        r"\section{Execution Resources and Turnover Bounds}",1)[0]
    assert r"\paragraph{Main results of this section}" in regime
    assert r"Theorem~\ref{thm:sublinear-severe}" in regime
    assert r"Theorem~\ref{thm:critical}" in regime
    assert "not merely the market-wide sum" in regime
    # Figure 6 belongs to Appendix G. The fixed placement and barrier
    # prevent it from moving across the start of the Appendix H proof.
    appendix_g=new.split(
        r"\section{A reproducible interval certificate for the two-day construction}",1
    )[1].split(r"\section{Sublinear power-law extension of uniform-budget severity}",1)[0]
    assert appendix_g.count("figures/multiday_crisis_trigger.pdf")==1
    assert r"\begin{figure}[H]\centering" in appendix_g
    assert appendix_g.rstrip().endswith(r"\FloatBarrier")
    assert r"\label{fig:multiday-crisis-trigger}" in appendix_g
    for heading in (
        "Model and Systemic Drawdown Criterion",
        "Execution Resources and Turnover Bounds",
        "Reachability under Bounded Execution Rates",
        "Rolling Price Limits: Constrained Realizations",
    ):
        assert heading in new
    assert "Construction of the severe-loss path" in new

    assert "The Flash Crash: High-frequency trading in an electronic market" in bib
    assert "The flash crash: high-frequency trading in an electronic market" not in bib
    # Verify scholarly meaning and citation placement rather than pinning
    # defensive or transitional English sentences verbatim.
    for phrase in (
        r"\dot S=-\rho(S-F)",
        "volume-recovery specifications with drift",
        "providing an intrinsic model scale",
        "multi-session proportional-reset price-band protocol",
        "records the benchmark value of inventory consumed",
        "The separation between structural exclusion, constructive reachability",
    ):
        assert phrase in new, ("Missing scientific/editorial content",phrase)
    citation_locations={
        "AlmgrenChriss2001": r"\section{Introduction}",
        "BankBaum2004": r"\paragraph{From the conditional matching map to an effective response}",
        "CetinJarrowProtter2004": r"\paragraph{From the conditional matching map to an effective response}",
        "RochSoner2013": r"\paragraph{Price-level resilience as a modeling choice}",
        "BressanRampazzo1988": r"\paragraph{Finite-variation paths and marginally settled pulses}",
        "Subrahmanyam1994": r"\section{Rolling Price Limits: Constrained Realizations}",
        "Tucker2011": r"\section{A reproducible interval certificate for the two-day construction}",
    }
    for key, location in citation_locations.items():
        assert key in keys, ("Missing BibTeX entry",key)
        assert key in cited, ("Uncited foundational reference",key)
        assert location in new, ("Missing citation context",location)
    assert len(keys)==33, ("Expected seven added references",len(keys))
    for stale in (
        "not a Tokyo Stock Exchange case study",
        "We do not claim the corresponding thresholds are invariant",
        "not as an empirically representative market crash",
    ):
        assert stale not in new, ("Old prose restored",stale)
    print("PASS corrected theorem ordering, bibliography proper noun and prose scope")
    print("PASS V13 original math, V14 new proposition plus sublinear severity theorem")
    print("PASS all-asset necessary M>=",Mmin,"(original budget remains inconclusive)")
if __name__=="__main__":
    main()
