"""Static identity checks for the V13 review-response candidate."""
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
OLD = ROOT / "submission/siam-language-revision"
NEW = ROOT / "submission/v13-review-response"

def numbered_results(src):
    pattern = r"\\begin\{(assumption|definition|theorem|proposition|lemma)\}(?:\[[^\]]*\])?[\s\S]*?\\end\{\1\}"
    return re.findall(pattern.replace("(assumption|definition|theorem|proposition|lemma)", "(?:assumption|definition|theorem|proposition|lemma)"), src)

def environment_bodies(src):
    result = []
    for name in ("assumption", "definition", "theorem", "proposition", "lemma"):
        result.extend((name, block) for block in re.findall(
            rf"\\begin\{{{name}\}}(?:\[[^\]]*\])?[\s\S]*?\\end\{{{name}\}}", src))
    return sorted(result)

def labelled_equations(src):
    return re.findall(
        r"\\begin\{equation\}[\s\S]*?\\end\{equation\}", src)

def main():
    baseline = (OLD / "main.tex").read_text(encoding="utf-8")
    candidate = (NEW / "main.tex").read_text(encoding="utf-8")
    bib = (NEW / "references.bib").read_text(encoding="utf-8")
    assert environment_bodies(baseline) == environment_bodies(candidate), (
        "Numbered statement differs from published English edition")
    assert labelled_equations(baseline) == labelled_equations(candidate), (
        "Existing numbered equation changed")
    old_labels = set(re.findall(r"\\label\{([^}]+)\}", baseline))
    new_labels = set(re.findall(r"\\label\{([^}]+)\}", candidate))
    assert old_labels.issubset(new_labels), ("Missing old labels", old_labels-new_labels)
    keys = re.findall(r"@\w+\s*\{\s*([^,\s]+)\s*,", bib)
    assert len(keys) == len(set(keys)), "Duplicate BibTeX keys"
    used = set()
    for group in re.findall(r"\\cite[pt]?\s*\{([^}]+)\}", candidate):
        used.update(k.strip() for k in group.split(","))
    assert used <= set(keys), ("Missing bibliography keys", used-set(keys))
    assert all(k in used for k in (
        "AlfonsiFruthSchied2010", "CuratoGatheralLillo2017",
        "SchneiderLillo2019", "BenzaquenEtAl2017",
        "BrunnermeierPedersen2005", "KirilenkoEtAl2017",
        "ContSchaanning2017", "BucciEtAl2019"))
    print("PASS: V13 numbered statements and equations retained; citations resolve")
    print("Baseline citations:", len(set(re.findall(r"\\cite[pt]?\s*\{([^}]+)\}", baseline))))
    print("V13 unique citation keys:", len(used))

if __name__ == "__main__":
    main()
