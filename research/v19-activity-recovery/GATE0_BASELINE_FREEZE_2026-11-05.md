# V19 activity-driven model — Gate 0 provenance and baseline freeze

Status: **GATE 0 CLEARED (source/provenance only)**. Date: 2026-11-05. This is NOT mathematical Gate 1/2 clearance, a certified construction, a manuscript release, or a replacement for V16.

## Sources frozen for subsequent audit

- Original author PDF: `original_manuscript_40p.pdf` in the supplied V19 checkpoint: **40 pages**. Its figure/table content must be inspected separately from the TeX figure-environment count.
- Source V16: `submission/v16-three-certified-constructions/main.tex` (GitHub blob `f3c4659eb96a0ff4c6c4c84434eb3c01ad231a2e`; 1,670 lines), `shared.tex` (`69ee01b680f9e102e0b8f5bd32d2ad85aa7e2eb2`), `references.bib` (`f5ebe530c08ce5d12a89b227a1677c440a07c1c6`; 33 entries), and `docs/VERSIONS.md` (`6ef14cc202aa6c73a612384307508efb135c1d56`). Read from `main` at `703846df04d373a17638804151bda16ffca032d8`.
- V17 prior: checkpoint `v17_package/submission/v17-activity-driven-recovery/{main.tex,shared.tex,references.bib}`, `v17_package/verification/activity_driven/certify_five_targets.py` and `five_target_certificate.json`, plus historical draft PR #48. Its reduced manuscript is **not** the coverage baseline.
- V19 source: `V19_GATE_CHECKPOINT_ZH.md`, `V19_MATHEMATICAL_GATE_REVIEW_ZH.md`, `V19_TRACEABILITY.csv/.md/.json`, `README.md`, verification scripts and datasets, 6 PDF figures, earlier research package, and previous analytic-review notes.
- Supplied V19 archive in this conversation is a **repackaged outer ZIP** with SHA-256 `80f1b7744899f15ca31a3904467ee8f43454c9d7af50da8b84666a1c6193b35d`, different from the earlier handoff's stated checksum for a differently named inner archive. All entries covered by the unpacked V19 `SHA256SUMS` passed local checksum verification. This distinction is not evidence of file tampering.

## Model frozen (old external-time restoration excluded)

```text
dS_i = [g(S_i)/S_i] dX_i - kappa (S_i-F) dA_i
dX_i = sum_e B_ie dz_e,   dA_i = sum_e |B_ie| dz_e,   dz_e >= 0
```

Complete bidirected graph without self-edges; a trade is completed by integrating the combined impact/recovery event ODE through its positive dollar amount. Prices stay strictly positive, `S_i(0)=F>0`, terminal `X_i(T)=0` individually, and nonnegative initial holdings must cover **true seller-side shares** `H_i^- = sum_{e: B_ie=-1} integral dz_e/S_i`. Total paired-dollar turnover counts each edge once: `M=(1/2) sum_i A_i(T)`.

`C0` permits simultaneous opposite genuine gross flows at one node, `C1` disallows them at each active instant, but permits sequential round trips. No trading implies no recovery. Power-law `g_p(S)=eta (S/F)^p`; normalized `dx_i=x_i^{p-1}du_i-K(x_i-1)da_i`, `K=kappa F^2/eta`. Crisis is **terminal** `C_alpha(T)=min(mean log(F/S_i(T)), kth-largest log loss)`, `k=ceil(alpha N)`. This is deterministic reachability, not probabilities or an optimal trading prescription.

## Construction identities, not certified parameter sets

- I: N=10, p=0, auxiliary rho=0.4, T=40, activity rate a0=30, K=1/75, total turnover 6000, smoothing h=0.2; this is a **floating-point candidate**, not an interval-certified specific root.
- II: N=10, p=0, rho=1, T=4, c=0.001, h=0.012, a0=500, K=0.002, turnover 10000; q=1e-2/1e-4/1e-8 are **floating-point cases**. Independent analytic existence uses other choices and cannot transfer its certification to these cached parameters.
- III: N=10, p=0, K=2, two sessions [0,20], [20,40], 5 targets close at 3/4 then 9/16 in C1. Existing 19-edge/five-cycle evidence is **INTERVAL_INTERNAL** from one implementation, not an independent external second certificate or a proof of maximum breadth.

## Completeness lock

All **43 unique IDs** remain active: M01–M03 (3), T01–T09 (9), P01–P12 (12), L01 (1), I01–I03 (3), R01–R03 (3), A01–A08 (8), F01–F03 (3), B01 (1). Each research item must keep the mapping to historical question, new-model assumptions, claim, source paths, evidence level, acceptance obligation, and impact on strong abstract claims.

Open/partial mathematical audits inherited at this gate: `T03 P02 T04 T05 P10 P11 P12 I01 I02 R01 R02 R03 A03 A04 A07`. Previous internal analytic proof drafts are research priors; their correctness is not implied by Gate 0 clearance. Evidence distinctions: `ANALYTIC_PROOF`, `INTERVAL_INTERNAL`, `NUMERIC_ONLY`, and `OPEN/PARTIAL/PROOF_TO_AUDIT`.

## Executed local scope

- Verified unpacked V19 file hashes with `sha256sum -c SHA256SUMS`: exit 0.
- Checked original PDF page count programmatically: 40.
- Read original LaTeX result/appendix hierarchy: nine theorem, twelve proposition, one lemma, eight appendices, 33 V16 bibliography entries.
- Verified updated matrix retains 43 IDs and distribution above.
- Reran `run_v19_gate_checks.py`: exit 0, while it explicitly prints the 15 unresolved mathematical gates. This is a **regression and traceability check**, not theorem verification.

## Stop/go statement

**Gate 0 is cleared as provenance/coverage freeze only.** Gate 1 (independent mathematics), Gate 2 (three fully certified constructions), Gate 3 (complete scientific manuscript), and Gate 4 (independent build and two editable bilingual Word deliverables) are **NOT CLEARED**. Keep all previous V16/V17 source, artifacts, historical DOI and releases untouched.
