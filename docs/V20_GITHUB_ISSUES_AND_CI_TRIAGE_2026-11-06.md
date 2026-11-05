# Open GitHub issues and current V20 Gate 3 — scope-separated triage

Date: 2026-11-06. **This is a status/ownership register, not a theorem or release announcement.**

A GitHub Actions status, a V20 *internal analytic proof draft*, and completion of a historically specified **Lean kernel proof** are three different evidence types. Old V12/V14 assertions contain physical-time restoration; V20's activity-clock dynamics are not equivalent, and cannot be used to close their historical formalization tasks.

## Open issues verified against GitHub issue bodies

| Issue | Historic task | Required action | Current resolution / relation to V20 |
|---|---|---|---|
| [#5](https://github.com/Siyuan-chat/market-crash-reachability/issues/5) | V12 English paper complete kernel-backed Lean crosswalk | Complete all theorem-to-declaration proof contracts | **OPEN**: historical umbrella; green CI only checks existing subset |
| [#8](https://github.com/Siyuan-chat/market-crash-reachability/issues/8) | V12 physical BV/Stieltjes chain rule & full no-crash invariant | Formalize the actual physical-price model without assuming its desired coordinate identity | **OPEN**: not supplied by V20 event-completed lemma |
| [#37](https://github.com/Siyuan-chat/market-crash-reachability/issues/37) | V14 A1 88-second source-faithful animation handoff | Create, compare against V14 A1 witness and deliver media/provenance | **OPEN**: non-blocking for V20 Gate 3 manuscript |
| [#40](https://github.com/Siyuan-chat/market-crash-reachability/issues/40) | V14 general fixed `0<=p<1` uniform-resource **Lean** theorem | Fully kernel-check the V14 physical-time theorem with the quantifiers and inventory assumptions specified | **OPEN**: V20's internally reviewed activity-driven analytic derivation is *not* the required V14 Lean theorem |
| [#41](https://github.com/Siyuan-chat/market-crash-reachability/issues/41) | V14 unmatched-dollar stability Lean | Formalize original V14 time-restoration bound and integrability | **OPEN**: V20 manuscript has a different conditional stability estimate |
| [#42](https://github.com/Siyuan-chat/market-crash-reachability/issues/42) | V14 heterogeneous quadratic bound/two-pulse Lean | Prove full V14 exponential endpoint formulas and dynamic counterexample in kernel | **OPEN**: V20's event-completed local counterexample is a different theorem |
| [#43](https://github.com/Siyuan-chat/market-crash-reachability/issues/43) | V14 turnover–dissipation Lean | Prove the full AC physical-session identity and resource bound | **OPEN**: old restoration model, not the current V20 one |
| [#44](https://github.com/Siyuan-chat/market-crash-reachability/issues/44) | V14 exact rational interval witness proof checks | Prove strict resource, price and full ledger equalities with certified interval checker | **OPEN**: separate from V20 Construction III dual *internal* implementation |

## CI failures and repairs tracked separately

- [PR #63](https://github.com/Siyuan-chat/market-crash-reachability/pull/63) **merged**: fixed current editorial hash pins without rewriting original release or V14 manifests, corrected Markdown inline-code parsing, restored 43-row V20 CSV. Remote Reproducibility, Documentation consistency and V20 coverage checks all passed on its reviewed head.
- [PR #64](https://github.com/Siyuan-chat/market-crash-reachability/pull/64) **under CI review**: pinned `leantar 0.1.15` installation from locked source to bypass a 92-byte broken upstream release archive; must still pass `lake build` and Lean axiom integrity audits. This is a **toolchain repair, not a Lean theorem acceptance**.
- [PR #65](https://github.com/Siyuan-chat/market-crash-reachability/pull/65) **under CI review**: builds V20 with real SIAM and the intact original 33-entry V16 bibliography. Historical SIAM workflow is not evidence of this V20 build.

## Forward action and acceptance criteria

1. Restore **green reproducibility, documentation, coverage and full Lean current-kernel CI** by fixing causes while retaining strict checks; do not disable workflows for a green badge. Blocker classes: source code/tool availability vs actual mathematical kernel failure.
2. Produce and retain V20's real SIAM PDF/.bbl/.log and hash-bearing build report; reject unresolved citations or missing original references.
3. Maintain separate V12/V14 historical formalization tasks as open until their exact issue acceptance criteria are proved; do not silently convert older statements to the V20 model or close issues because the new model exists.
4. For V20 Gate 3, finish independent line-by-line mathematical review, report each of 43 items as proved / bounded / open, and only then record Gate 3 acceptance. Translation/Word is later Gate 4.
5. If issue owners decide the legacy model is superseded, formally close/relabel with a **human-reviewed scope decision**, not a silent automated change.

**No older issue is being marked resolved by this triage.**
