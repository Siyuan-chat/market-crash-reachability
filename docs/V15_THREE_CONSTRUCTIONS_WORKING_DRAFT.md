# V15 focused revision — working draft, 2026-10-22

## Main question and claim

We ask whether severe joint terminal price losses can be constructed by admissible trading paths in an explicitly idealized fixed-fundamentals market with positive prices, resilient price impact, paired-dollar execution, no short sales, and assetwise terminal dollar closure. The main contribution is a **constructive existence proof** under the stated model rules; structural exclusions and resource inequalities delineate this result, rather than displacing it.

The introduction, abstract, and conclusion must use consistent, confident language about what has **actually been proved**. Model conditions are part of theorem statements. Do not add a real-world legal, regulatory, derivatives, general-equilibrium, margin-call, or agent-behavior model to the main claim.

## The only three main constructions

1. **Ten assets, all fall:** the existing exact analytical construction of ten assets ending at half their benchmark prices. Price response constant; impulsive flow-completed execution permitted.
2. **Ten assets, nine fall:** the existing analytical single-compensator construction giving nine arbitrarily severe partial-coverage log losses with finite severity-independent turnover and inventory bounds.
3. **Ten assets, two consecutive 25% lower-limit closes:** **NOT YET PROVED**. The final target uses a uniform ±25% rolling band for **all ten assets** in two sessions. A rigorously determined nonempty subset of target assets must close at 0.75 and 0.5625 of its initial fundamental benchmark on the first and second session respectively, with finite gross share rates and inventories, pairing at each trade, and each dollar ledger closing to zero at the horizon.

Do **not** assert k=7, k=8, or k=9 is reachable until a qualifying control and interval certificate are completed. The original 3% lower-close certificate and the existing uniform-band >20.2% terminal-loss certificates are different results. They may remain available as archival research inputs, but they are not interchangeable with Construction III.

## Work already performed in this branch

- Rewrote abstract, introduction, discussion, conclusion around the two **proved** ten-asset severe-loss existence statements.
- Named exactly Construction I, II, and III in the main narrative; removed A1/A2/B1/B2 and P/R benchmark codes from the paper body.
- Expanded the main-text proof of the fixed-resource partial-coverage result, exposing the stagewise radial control, compensator-root argument, recovery-weight partition, terminal dollar closure and uniform budget bounds.
- Retained the complete analytic source proofs for the first two constructions in the appendices.
- Replaced the obsolete 3% main-text witness and the many non-limit-down variants with a clear, unproved, mathematically specified Construction III target and conditional necessary resource/index estimates. This is a **draft**, not a final result.
- Removed N=3/N=12/N=20 numerical examples and additional benchmark tables from the manuscript; numerical research assets remain in the repository.
- Shortened the discussion without introducing extra real-market mechanisms.

## Proof/certification gate for Construction III

A final proposition may be placed in the main paper only when an independent validation step confirms:
- exact terminal target closes in both sessions (including the reset), not approximate large declines;
- strictly positive prices and *every* continuous intraday band;
- positive paired executed-dollar transfers, individually closed terminal dollar ledgers;
- gross executed share rates, gross sales, and total matched-dollar turnover under reported finite caps;
- nontrivial coverage k and a numerical certification that encloses the ODE flow and the claimed terminal inequalities;
- a main-text construction/proof readable without having to execute code, with detailed outward-rounded estimates in supplemental material.

Only then update the V15 abstract/introduction/conclusion to include the proven third witness and remove the explicit working-draft qualification.

## CI and preservation

The old V14 directory and its historical acceptance test remain unchanged. V15 gets its own build, editorial integrity check, and GitHub Actions PDF artifact. Do not merge this draft as the final paper while Construction III remains uncertified.
