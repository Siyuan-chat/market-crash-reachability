# Verification scope

The manuscript's analytic arguments are paper proofs. The symbolic checks
cover specified coordinate identities; numerical regressions cover selected
parameter cases. Neither constitutes machine formalization of the theorems.

Proposition 7.6 is a computer-assisted existence proof for the prescribed
N=10, k=9 path, F=eta=1, rho=0.4, two sessions of length 20, target bands
±3%, and compensator bands ±25%. The certifier checks positivity, daily bands,
endpoint dollar closure, gross rates and resource bounds. Exact rational
comparisons certify C_0.9(40)>0.020 (and <0.021), with
1.4047874<y(40)<1.4055543 and maximum gross rate <0.285.
It does not establish a globally optimal control or model real locked order
books, general equilibrium, empirical probabilities, or market predictions.

`verify_consistency.py` reads the final certificate and the numerical fixture;
it does not regenerate the enclosure. `audit_manuscript_certificate.py`
checks publication rounding and independently integrates the six-segment ODE.
Only `certify_streak_interval.py` regenerates the interval certificate.

The old names v7_rate_smoothed, v11_verified and v12 refer to byte-identical
copies of the final certificate in the supplied package. Their original hashes
are recorded in CERTIFICATE_PROVENANCE.json. The algorithm retains historical
V7 terminology internally because the witness originated then. No mathematical
logic or parameters were changed during repository organization.

The full suite also runs `verification/audit_sensitivity.py` with
`scripts/sensitivity_probe.py`: fixed-path 24.7%/24% band conclusions use the
existing outward enclosures, whereas alternative k<9 cases are ordinary ODE
diagnostics. They are not additional certified feasibility results. Review the
paper's availability paragraph after the public URL exists. No unapproved
manuscript wording was changed.
