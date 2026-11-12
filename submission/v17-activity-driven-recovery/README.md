# When Can Markets Crash Without News? — V17 working edition

This edition **replaces physical-time recovery by gross-trade-activity-driven resilience**. It is not the V16 paper with renamed variables.

- `main.tex`: English theoretical paper and analytical continuation arguments, including three ten-asset examples and explicit uncertainty/evidence boundaries.
- `references.bib`: separately scoped bibliography, seeded from V16 and checked by first citation order.
- `shared.tex`: SIAM template settings matching historical manuscript format; offline `article` preview fallback does not claim to be the actual SIAM build.
- `verification/activity_driven/certify_five_targets.py`: internal outward-rounded C1 certificate for example III.
- `verification/activity_driven/test_activity.py`: independent mathematical/numerical sanity regressions.
- `scripts/check_v17_activity.py` and `scripts/build_v17_activity.py`: independent claim consistency checks and strict CI manuscript build.
- `docs/V17_ACTIVITY_WORKING_DRAFT.md`: theorem/evidence matrix and open questions.

**Working manuscript; internal mathematical verification only.** Historical V16 and fixed DOI archival snapshots are untouched.
