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

def main():
    old=OLD.read_text(encoding="utf-8")
    new=NEW.read_text(encoding="utf-8")
    assert result_blocks(old)==result_blocks(new),"V13 numbered statements changed"
    pat=r"\\begin\{equation\}[\s\S]*?\\end\{equation\}"
    assert re.findall(pat,old)==re.findall(pat,new),"V13 numbered equations changed"
    assert set(re.findall(r"\\label\{([^}]+)\}",old)) <= set(re.findall(r"\\label\{([^}]+)\}",new))
    for term in ("Turnover--dissipation screening under bounded prices",
                 "Illustration for a uniform two-session rolling band",
                 r"\sum_i|\dot X_i(t)|\le2\dot M(t)",r"\mathrm e=\exp(1)",
                 r"M(T)\ge0.5382"):
        assert term in new,("Missing scope/proof",term)
    assert r"\sum_i|\dot X_i(t)|=2\dot M(t)" not in new
    block = new.split(r"\paragraph{Turnover--dissipation screening under bounded prices}", 1)[1].split(r"\section{Finite trading rates and abstract price bands}", 1)[0]
    assert r"q_i(t)=\dot X_i(t)" not in block, "Collision with log-price variable q_i"
    assert r"1.02020225507905<h<1.02020225507908" in new, "Correct interval missing"
    assert "1.020225507905" not in new, "Incorrect left endpoint reappeared"
    f = lambda z: 101600000000*z*z - 97138000000*z - 6646157699
    getcontext().prec=60
    assert f(Decimal("1.02020225507905")) < 0 < f(Decimal("1.02020225507908"))
    assert "the hypothetical original-budget targets" not in new
    assert "failure to find a control by numerical optimization" not in new
    assert "This unpublished research draft" not in new
    for title in ("Crossover from linear to square-root market impact",
                  "Fire sales, indirect contagion and systemic stress testing",
                  "The flash crash: high-frequency trading in an electronic market"):
        assert title in bib, ("Bibliography case",title)
    bib=(NEW.parent/"references.bib").read_text()
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
    print("PASS V13 theorem/equation/label preservation, citations, exact endpoint arithmetic")
    print("PASS all-asset necessary M>=",Mmin,"(original budget remains inconclusive)")
if __name__=="__main__":
    main()
