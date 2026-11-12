# When Can Markets Crash Without News? Activity-Driven Recovery and Systemic Reachability


> **Gate 4 review-source derivative.** Generated from native editable Word for bilingual review. The frozen scientific authority remains `submission/v20-gate3-activity-recovery/main.tex` (SHA-256 `9d36ab61019bcb395073918c133bfc4a4cf23c32b99efd9a84c021fb7d092baa`). Equations rendered here by Pandoc are a readable, noncanonical Markdown representation; preserved, editable OMML in the DOCX is the Word authority. Figures below link to frozen vector PDFs. Gate 4 is not fully cleared because of quantified renderer exceptions.

Siyuan Ye

Abstract

Matched-dollar transfers can produce systemic terminal price losses even when fundamental benchmarks are fixed and every asset's cumulative executed-dollar ledger closes at zero. We replace recovery in physical time by recovery driven exclusively by gross executed-dollar activity. The resulting nonlinear control system has no price motion without transactions. A nine-edge three-asset protocol establishes local all-asset declines for arbitrary smooth positive response functions, while scalar activity floors and execution-resource inequalities restrict severe losses. Heterogeneous quadratic responses can also produce a two-node systemic loss through a closed, sequential dollar round trip, despite the homogeneous quadratic obstruction. For homogeneous two-node power laws with $1 < p \leq 3/2$, a finite-size reversal produces systemic loss despite the small-turnover barrier. For each fixed $K$, this finite-budget region extends to a nonempty exponent interval above $3/2$ by continuity of the exact price-response flows. One explicit $\mathsf{C}_{1}$ witness uses $p = 5/4$, $K = 1$ and only eight units of paired turnover. In the constant-impact model, a continuous-direction argument gives an analytic existence construction for all ten prices to end at half their benchmarks. For every fixed power-law exponent $0 \leq p < 1$, nine prices can become arbitrarily small under one common finite turnover and inventory envelope (with constants depending on $p$). A separate cross-checked internally interval-verified, no-instantaneous-netting ten-asset path makes five assets close at the lower limit of successive $\pm 25\%$ rolling sessions. The path has finite gross share-execution rate and an equal-weight geometric-index loss above $16\%$. These are deterministic reachability results, not equilibrium crash predictions.

**Keywords.** market crashes; trade activity; price impact; systemic drawdown; reachability; interval verification; execution constraints

**MSC codes.** 91G15, 91G45, 93B03, 65G30

# 1. Introduction

Crashes may accompany public news, forced selling, liquidity withdrawal or information revealed by trades. Their respective theoretical mechanisms are studied, among others, by \[10\], \[15\], \[11\], \[6\], and \[8\]. The predatory-trading mechanism studied by \[5\] introduces strategic reactions that are intentionally absent from our model. These explanations are distinct from a deterministic existence proof: they posit endogenous information or incentives that may induce particular trades, whereas we test which price endpoints are mechanically compatible with the execution and settlement constraints. An independent mathematical question is whether a price decline is compatible with a fully paired stream of trades whose *cumulative dollar balance in each asset* is zero. This is a reachability question, not an explanation of any particular historical crash.

Resilient execution models typically assign time dynamics to the liquidity state; see \[14\], \[1\]. We instead ask what changes when price resilience is triggered only by gross dollar activity associated with actual trades. Such activity can be strictly positive even when a node's simultaneous net executed-dollar flow vanishes. It is therefore essential to distinguish a permissive control class from a stricter class in which each node can only buy or only sell at a given instant. Our model is an explicitly parameterized price-response law, not a strategic equilibrium or a no-manipulation result of the type considered by \[9\], \[12\]. Large-trader and liquidity-adjusted pricing frameworks \[3\], \[7\] offer a related motivation for state-dependent execution responses, without identifying their equilibria or supply curves with the activity-driven law defined here.

We provide a self-contained analytic reachability chain and one narrow computer-assisted construction. The universal results are local triangular reachability, scalar floors, an aggregate full-coverage barrier, and necessary turnover and inventory bounds. The ten-asset results are: (I) all ten terminal prices equal one half of the benchmark; (II) nine losses have no finite severity ceiling while time, turnover and inventory are bounded by one set of constants; and (III) the same five assets close at the lower limits of two consecutive $\pm 25\%$ sessions under the stricter no-instantaneous- netting class. The first two are analytic existence constructions whose parameters need not coincide with the old physical-time model's numerical budgets. We also derive a heterogeneous weighted-log balance and a closed-ledger two-node counterexample; unlike the earlier physical-time weighted-flow estimate, neither relies on a recovery term when no trades occur. The third has a reproducible, internally outward-rounded certificate. No earlier fixed-version manuscript or its numerical certificate is represented as a certificate for the present dynamics.

# 2. The activity-driven paired-dollar market

Fix $N \geq 2$, a fixed benchmark $F > 0$, positive transaction prices $S_{i}$, and a positive locally $C^{2}$ response $g$. The complete bidirectional graph without self-edges has incidence matrix $B$: for an edge from seller $i$ to buyer $j$, $B_{ie} = - 1$ and $B_{je} = 1$. A control is a vector of nonnegative edge-flow measures $\, dz_{e}$. The *executed-dollar ledger* and *gross dollar activity* of asset $i$ are

$$\, dX_{i} = \sum_{e}^{}B_{ie}\, dz_{e},\quad\quad\, dA_{i} = \sum_{e}^{}\left| B_{ie} \right|\, dz_{e},\quad\quad\boxed{\, dS_{i} = \frac{g\left( S_{i} \right)}{S_{i}}\, dX_{i} - \kappa\left( S_{i} - F \right)\, dA_{i}},\quad\kappa > 0.$$ (2.1)

The sums $\sum_{i}^{}\, dX_{i} = 0$, $\sum_{i}^{}\, dA_{i} = 2\sum_{e}^{}\, dz_{e}$, and the nodewise inequality $\left| \, dX_{i} \right| \leq \, dA_{i}$ follow from incidence accounting. A direct edge transfer of dollar mass $z > 0$ is integrated in its own amount parameter $a \in \lbrack 0,z\rbrack$, including *both* terms in (2.1), with $\, d\theta_{i} = \, dX_{i}/S_{i}$ for share positions. Finite sequences of such flows and absolutely continuous rates are admissible while all intermediate prices are positive. This flow-completed convention preserves the usual chain rule; an old rule in which recovery freezes during a trade is *not* used here. Graph-completed impulsive-control systems provide a related mathematical framework \[4\], but the present ordered-edge prescription is an explicit modeling assumption, not a general assertion of path-order independence. If $\, dz = 0$, prices do not move.

**Definition 2.1** (Controls and execution resources). *In* $\mathsf{C}_{0}$ *every nonnegative edge flow is allowed, including simultaneous inflow and outflow at one vertex. In* $\mathsf{C}_{1} \subset \mathsf{C}_{0}$*, each asset is a pure dollar buyer or a pure dollar seller almost everywhere on active periods; equivalently* $\left| {\dot{X}}_{i} \right| = {\dot{A}}_{i}$ *when* ${\dot{A}}_{i} > 0$*. Switching direction over time is permitted in both classes. All paths start at* $S_{i}(0) = F$ *and impose* $X_{i}(T) = 0$ *for every asset. The paired turnover and cumulative sales in shares are* $$M = \sum_{e}^{}{\int_{0}^{T}\,}dz_{e} = \frac{1}{2}\sum_{i}^{}A_{i}(T),\quad\quad H_{i}^{-} = \sum_{e:\, B_{ie} = - 1}^{}{\int_{0}^{T}\frac{\, dz_{e}}{S_{i}}};$$ (2.2) *when control is absolutely continuous the gross share-execution rate is* $r_{i}^{gross} = {\dot{A}}_{i}/S_{i}$*. In* $\mathsf{C}_{0}$*,* $H_{i}^{-}$ *counts actual gross share sales even when simultaneous purchases cancel net executed dollars; the net negative variation of* $X_{i}$ *would undercount those sales. Starting inventory* $H_{i} \geq H_{i}^{-}$ *prevents short sales. Dollar closure does not require share-flatness.*

For power responses let

$$g_{p}(S) = \eta(S/F)^{p},\quad D_{F} = F^{2}/\eta,\quad x_{i} = S_{i}/F,\quad u_{i} = X_{i}/D_{F},\quad a_{i} = A_{i}/D_{F},\quad K = \kappa D_{F}.$$ (2.3)

The uniquely relevant normalized dynamics are

$$\boxed{\, dx_{i} = x_{i}^{p - 1}\, du_{i} - K\left( x_{i} - 1 \right)\, da_{i}},\quad\quad\left| \, du_{i} \right| \leq \, da_{i},\quad\sum_{i}^{}\, du_{i} = 0.$$ (2.4)

In the power-law sections, dollars, shares, and prices are explicitly normalized by $F = \eta = 1$ where indicated. The absence of a calendar-time resilience term makes the following time-scale statement exact; it replaces, rather than inherits, the old physical-time model's critical-horizon theorem.

**Proposition 2.2** (No intrinsic horizon threshold without gross-rate caps). *Fix the response law, the trading graph, the model parameters, and a strictly positive admissible path on* $\lbrack 0,T\rbrack$*,* $T > 0$*, formed from absolutely continuous nonnegative paired edge-dollar rates and, optionally, finitely many ordered flow-completed edge events, with finite turnover and genuine share inventories. For every* $T\prime > 0$ *there is an admissible path on* $\lbrack 0,T\prime\rbrack$ *in the same class* $\mathsf{C}_{0}$ *or* $\mathsf{C}_{1}$ *with precisely the same terminal prices, individual terminal dollar ledgers, paired turnover, and gross seller-share quantities. In particular, a terminal market loss reachable on some positive horizon is reachable on every positive horizon, so there is no nonzero calendar-time critical horizon in the model without a gross-rate constraint. The conclusion does not imply that a loss state is reachable at all; structural price and budget barriers still apply.*

*Proof.* For an arbitrary $T\prime > 0$ put $\lambda = T/T\prime$ and, for $t \in \lbrack 0,T\prime\rbrack$, define

$${\widetilde{S}}_{i}(t) = S_{i}(\lambda t),\quad{\widetilde{X}}_{i}(t) = X_{i}(\lambda t),\quad{\widetilde{A}}_{i}(t) = A_{i}(\lambda t),\quad{\dot{\widetilde{z}}}_{e}(t) = \lambda{\dot{z}}_{e}(\lambda t) \geq 0.$$

The absolutely continuous chain rule and the fact that (2.1) has no free $\, dt$ term show that these transformed paths satisfy the same activity-driven model. Their prices remain positive and every edge retains its original incidence signs and transaction ordering. The nodewise buyer/seller exclusivity required by $\mathsf{C}_{1}$ is invariant under this positive time change. For each of finitely many ordered flow-completed edge events, transport its calendar timestamp $\tau$ to $\tau/\lambda$ while retaining its executed dollar amount and its relative ordering. The event ODE is parameterized by executed dollar amount, not elapsed time; hence its completed positive-price map and share increment are identical before and after time rescaling. Changing variables in the cumulative executed-dollar, turnover and genuine gross share-sale integrals proves

$${\widetilde{X}}_{i}(T\prime) = X_{i}(T),\quad\quad\widetilde{M} = M,\quad\quad{\widetilde{H}}_{i}^{-} = H_{i}^{-},\quad\quad{\widetilde{S}}_{i}(T\prime) = S_{i}(T).$$

Thus terminal dollar closure and systemic losses are unchanged. By contrast, the gross share rate transforms as ${\widetilde{r}}_{i}^{gross}(t) = \lambda r_{i}^{gross}(\lambda t)$. Consequently the argument does not preserve a fixed cap $r_{i}^{gross} \leq v$ when $\lambda > 1$. ◻

**Definition 2.3** (Terminal systemic crisis). *Write* $L_{i}(T) = \log\left( F/S_{i}(T) \right)$*,* $\bar{L} = N^{- 1}\sum_{i}^{}L_{i}$ *and* $k = \lceil\alpha N\rceil$*. If* $Q_{\alpha}$ *is the* $k$*th largest* $L_{i}$*, define* $$\mathcal{C}_{\alpha}(T) = \min\{\bar{L}(T),Q_{\alpha}(T)\}.$$ (2.5) *The terminal event is* $\mathcal{C}_{\alpha}(T) \geq \delta > 0$*; neither rolling peak drawdowns nor first-passage times are identified with this criterion.*

## 2.1. Exact transformed accounting

Define for positive prices

$$\Phi(S) = \int_{F}^{S}\frac{v}{g(v)}\, dv,\quad\Psi(S) = \int_{F}^{S}\frac{\, dv}{g(v)},\quad E(S) = \int_{F}^{S}\frac{v - F}{g(v)}\, dv \geq 0,\quad R(S) = \frac{S(S - F)}{g(S)}.$$ (2.6)

**Proposition 2.4** (The activity balance and execution cost). *For each flow-completed path,* $$\begin{matrix}
\, d\Phi\left( S_{i} \right) & = \, dX_{i} - \kappa R\left( S_{i} \right)\, dA_{i}, \\
\, d\left\lbrack \sum_{i}^{}\Phi\left( S_{i} \right) \right\rbrack & = - \kappa\sum_{i}^{}R\left( S_{i} \right)\, dA_{i}, \\
X_{i}(T) & = F\,\left\lbrack \theta_{i}(T) - \theta_{i}(0) \right\rbrack + E\left( S_{i}(T) \right) + \kappa\int\frac{\left( S_{i} - F \right)^{2}}{g\left( S_{i} \right)}\, dA_{i}.
\end{matrix}$$ (2.7, 2.8, 2.9) *In particular, exact dollar closure and equal share positions both at* $0$ *and* $T$ *force a stationary price path. If* $X_{i}(T) = 0$ *and* $S_{i}(T) < F$*, then* $\int_{S_{i} > F}^{}R\left( S_{i} \right)\, dA_{i} > 0$*.*

*Proof.* Use $\Phi\prime(S) = S/g(S)$ in (2.1) to get (2.7); paired transfers cancel in (2.8). For the last identity, $\, dX_{i} = S_{i}\, d\theta_{i}$ and $\, dX_{i} - F\, d\theta_{i} = \left( S_{i} - F \right)\, dX_{i}/S_{i} = \left( S_{i} - F \right)\, dS_{i}/g\left( S_{i} \right) + \kappa\left( S_{i} - F \right)^{2}\, dA_{i}/g\left( S_{i} \right)$. Integrate and apply the chain rule to $E$. The last two nonnegative terms in (2.9) must both vanish under simultaneous closures. For $S_{i}(T) < F$, (2.7) with $X_{i}(T) = 0$ implies $- \Phi\left( S_{i}(T) \right) = \kappa\int R\left( S_{i} \right)\, dA_{i} > 0$; $R$ is positive only above $F$. ◻

# 3. Local all-asset reachability

For $g_{p}$ set

$$w_{p}(x) = \int_{1}^{x}s^{1 - p}\, ds = \left\{ \begin{matrix}
\left( x^{2 - p} - 1 \right)/(2 - p), & p \neq 2, \\
\log x, & p = 2,
\end{matrix} \right.\ \quad\quad r_{p}\left( w_{p}(x) \right) = x^{1 - p}(x - 1).$$ (3.1)

Then $\, dw_{i} = \, du_{i} - Kr_{p}\left( w_{i} \right)\, da_{i}$ with $r_{p}(0) = 0$ and $r_{p}\prime(0) = 1$. The same linearization works for a general smooth positive $g$ after scaling executed dollars by $F^{2}/g(F)$.

**Theorem 3.1** (Triangular local reachability). *On the complete bidirectional graph, for every* $N \geq 3$*,* $\kappa > 0$ *and every positive* $C^{2}$ *response* $g$ *near* $F$*, a finite* $\mathsf{C}_{1}$ *sequence has strictly positive intermediate prices,* $X_{i}(T) = 0$ *for every* $i$*, and* $S_{i}(T) < F$ *for every* $i$*. For a normalized power response its prices satisfy* $w_{i}(T) = - m_{i}Kz^{2} + O_{N}\left( z^{3} \right)$ *as* $z \downarrow 0$*, with* $m_{1} = m_{2} = N - 2$ *and* $m_{j} = 1$ *for* $j \geq 3$*.*

*Proof.* On a triple $(a,b,c)$ execute nine equal-mass oriented edges, in order:

$$a \rightarrow b,\ b \rightarrow c,\ c \rightarrow a,\ b \rightarrow c,\ c \rightarrow a,\ a \rightarrow b,\ c \rightarrow a,\ a \rightarrow b,\ b \rightarrow c.$$

Each vertex receives and sends exactly $3z$. Its six signs in its own activity clock are respectively $( - , + , + , - , + , - )$, $( + , - , - , + , + , - )$, and $( + , - , + , - , - , + )$. All three satisfy $\sum_{j}^{}\sigma_{j} = 0$ and $\sum_{j}^{}j\sigma_{j} = - 1$. In the transformed coordinate $r(w) = w + O\left( w^{2} \right)$, hence variation of constants gives

$$\begin{matrix}
w(6z) & = \sum_{j = 1}^{6}\sigma_{j}\int_{(j - 1)z}^{jz}e^{- K(6z - a)}\, da + O\left( z^{3} \right) \\
 & = Kz^{2}\sum_{j = 1}^{6}j\sigma_{j} + O\left( z^{3} \right) = - Kz^{2} + O\left( z^{3} \right).
\end{matrix}$$

Repeat the same triple protocol on $(1,2,j)$ for $j = 3,\ldots,N$. The shared vertices start the later protocols only $O\left( z^{2} \right)$ away from benchmark, so subsequent increments retain the displayed quadratic term; $m_{i}$ counts participation. Each edge is a one-directional sale/purchase at the instant of execution, hence it is in $\mathsf{C}_{1}$. For sufficiently small $z$ the full path stays in a compact positive price neighborhood; initial inventories covering its finite sales suffice. ◻

**Remark 3.2**. *The distinction between* $N \geq 3$ *and* $N = 2$ *matters. If* $N = 2$ *then both assets have identical activity clocks. If* $e(S) = Sg\prime(S)/g(S) \geq 1$ *on the path, concavity of* $\Phi$ *gives* $R(S) \leq \Phi(S)$ *and* $\, dH \geq - \kappa H\, dA$*, where* $H = \sum_{i}^{}\Phi\left( S_{i} \right)$ *and* $A$ *is the common clock. Since* $H(0) = 0$*, simultaneous losses of both assets are impossible. If* $e \geq 2$*, concavity of* $q \mapsto \Phi\left( Fe^{q} \right)$ *also excludes* $\mathcal{C}_{\alpha} > 0$ *by Jensen's inequality. Neither is a general* $N \geq 3$ *obstruction in this activity model.*

# 4. The two-asset boundary and partial coverage

The distinction between two and three assets does not arise from the number of possible signs in a dollar ledger: it arises from the fact that both assets of a two-node market must share the *same gross activity clock*. In a three-node market, one edge can change the activity of two nodes without changing the third. The resulting heterogeneity permits the nine-edge construction of Theorem 3.1.

**Proposition 4.1** (Two-node common-clock barriers). *Suppose* $N = 2$ *and the response elasticity* $e(S) = Sg\prime(S)/g(S) \geq 1$ *on the positive-price state domain traversed by an admissible dollar-closed path. Then both final prices cannot be strictly less than* $F$*. If also* $e(S) \geq 2$*, then* $\overline{L}(T) \leq 0$*, and hence* $\mathcal{C}_{\alpha}(T) \leq 0$ *for every* $0 < \alpha \leq 1$*.*

*Proof.* Every admissible edge increments both gross activity clocks equally, including when opposite edges are simultaneously active in $\mathsf{C}_{0}$. Let the common clock be $a$. Define $H = \Phi\left( S_{1} \right) + \Phi\left( S_{2} \right)$ and $R(S) = S(S - F)/g(S)$. Because $\Phi'' = (1 - e)/g \leq 0$ and $(R - \Phi)\prime = (S - F)\Phi''$, with $R(F) = \Phi(F) = 0$, one has $R(S) \leq \Phi(S)$ for every $S$ in the state domain. Thus $dH/da = - \kappa\left( R\left( S_{1} \right) + R\left( S_{2} \right) \right) \geq - \kappa H$, so $H \geq 0$ by Gronwall from $H(0) = 0$. Both prices below $F$ would imply $H < 0$. If $e \geq 2$, set $G(z) = \Phi\left( Fe^{z} \right)$. Then $G\prime > 0$ and $G''(z) = S^{2}\left\lbrack 2 - e(S) \right\rbrack/g(S) \leq 0$. Concavity gives $G\left( \left( \log\left( S_{1}/F \right) + \log\left( S_{2}/F \right) \right)/2 \right) \geq H/2 \geq 0$; monotonicity of $G$ gives nonnegative mean log return. ◻

**Theorem 4.2** (A local two-node power-law classification). *Fix* $N = 2$*,* $K > 0$ *and a power-law exponent* $p \geq 0$*. For* $0 \leq p \leq 1$*, a sufficiently small dollar-closed two-edge round trip has* $\mathcal{C}_{1/2}(T) > 0$*; for* $0 \leq p < 1$*, its average terminal log loss is* $$\bar{L} = \frac{K(1 - p)}{3}z^{3} + O\left( z^{4} \right) > 0.$$ (4.1) *For every fixed* $1 < p < 2$ *there exists* $\varepsilon(p,K) > 0$ *such that no terminally dollar-closed two-node path with total paired turnover* $A < \varepsilon$ *can have positive mean log loss. For* $p \geq 2$ *no positive terminal systemic loss is possible, regardless of the turnover budget. The result for* $1 < p < 2$ *is only a small-turnover exclusion, not an assertion of global unreachability.*

*Proof.* In node activity time $a$, write $w = \left( x^{\nu} - 1 \right)/\nu$, $\nu = 2 - p$ (using $w = \log x$ if $p = 2$) and $r(w) = x^{\nu - 1}(x - 1)$. For a two-edge reversed transfer of amount $z$ each, the two zero-order $w$ paths are $\pm a$ on $\lbrack 0,z\rbrack$ and $\pm (2z - a)$ on $\lbrack z,2z\rbrack$. Since

$$r(w) = w - \frac{1}{2}(p - 1)w^{2} + O\left( w^{3} \right),$$

the sum $H = w_{1} + w_{2}$ satisfies $H(2z) = - (2/3)K(1 - p)z^{3} + O\left( z^{4} \right)$ and each terminal $w_{i} = O\left( z^{2} \right)$. Expanding $\log x_{i} = w_{i} + O\left( w_{i}^{2} \right)$ then proves (4.1). One node has a strictly negative terminal $w_{i}$ of order $z^{2}$, so the coverage condition also holds. At $p = 1$ the equation for $H$ is exactly $H\prime = - KH$, therefore $x_{1} + x_{2} = 2$ at the terminal time; the prices differ on a nontrivial reverse pair and strict AM--GM gives $\bar{L} > 0$.

For $1 < p < 2$, put $b(w) = w - r(w)$, so $b(w) = (p - 1)w^{2}/2 + O\left( w^{3} \right)$. In a sufficiently small fixed neighborhood of zero choose constants $c,L,C > 0$ with $b(w) \geq cw^{2}$, $\left| r(w) \right| \leq L|w|$ and $\log x(w) \geq w - Cw^{2}$. Under the shared gross clock $a \in \lbrack 0,A\rbrack$, $w_{i}\prime = \sigma_{i} - Kr\left( w_{i} \right)$, $\left| \sigma_{i} \right| \leq 1$, $\sigma_{1} + \sigma_{2} = 0$ and $\int_{0}^{A}\sigma_{i}\, da = 0$. Gronwall bounds $\left| w_{i}(a) \right| \leq a\exp(KLa)$, so all admissible controls stay in the chosen neighborhood for small enough $A$. Let $J = \int_{0}^{A}\left( w_{1}^{2} + w_{2}^{2} \right)\, da$. Then

$$H(A) = K\int_{0}^{A}e^{- K(A - a)}\sum_{i}^{}b\left( w_{i}(a) \right)\, da \geq Kce^{- KA}J.$$

Terminal ledger closure and Cauchy--Schwarz yield $\sum_{i}^{}w_{i}(A)^{2} \leq K^{2}L^{2}AJ$. Consequently

$$\sum_{i}^{}\log x_{i}(A) \geq K\{ ce^{- KA} - CKL^{2}A\} J \geq 0$$

when $A$ is below a strictly positive threshold depending only on $p,K$. Finally $p \geq 2$ follows from Proposition 4.1. ◻

**Theorem 4.3** (Finite-budget two-node crises beyond the small-turnover barrier). *Fix* $N = 2$*,* $F = \eta = 1$*,* $K > 0$ *and* $1 < p < 3/2$*. There is a strictly positive, terminally dollar-closed, sequential* $\mathsf{C}_{1}$ *path of finite paired turnover, finite true seller-side share inventory, and finite gross share-execution rate for which* $\mathcal{C}_{1/2}(T) > 0$*. In particular, for* $p = 5/4$ *and* $K = 1$ *two reversed four-dollar transfers at unit dollar rate on* $\lbrack 0,4\rbrack$ *and* $\lbrack 4,8\rbrack$ *give a fully explicit witness satisfying* $$\begin{matrix}
T = 8,\quad M = 8,\quad X_{1}(T) = X_{2}(T) = 0, \\
H_{i}^{-} < 16,\quad\sup_{i,t}r_{i}^{gross}(t) < 4, \\
S_{1}(T)S_{2}(T) < \frac{7555}{7716} < 1,\quad\quad\mathcal{C}_{1/2}(T) > \frac{1}{2}\log\frac{7716}{7555} > 0.
\end{matrix}$$ (4.2) *The lower bounds on initial shares and the upper rate bound are genuine seller-side quantities, not net dollar variation.*

*Proof.* Write $r = p - 1 \in (0,1/2)$ and use each node's incident dollar amount as its activity clock. On an edge, the buyer and seller prices respectively solve

$$\frac{\, dx}{\, da} = f_{+}(x): = x^{r} - K(x - 1),\quad\quad\frac{\, dx}{\, da} = f_{-}(x): = - x^{r} - K(x - 1).$$

There is a unique attracting seller equilibrium $x_{-} \in (0,1)$, since $f_{-}(0 + ) = K$, $f_{-}(1) = - 1$, and $f_{-}\prime(x) = - rx^{r - 1} - K < 0$. There is also a unique attracting buyer equilibrium $x_{+} > 1$: the ratio $x^{r}/(x - 1)$ is strictly decreasing from $+ \infty$ to zero on $(1,\infty)$. The defining identity $K\left( x_{+} - 1 \right) = x_{+}^{r}$ yields

$$f_{-}\left( 1/x_{+} \right) = x_{+}^{r - 1} - x_{+}^{- r} < 0\quad\quad(r < 1/2).$$

As $f_{-}$ is strictly decreasing, $x_{-} < 1/x_{+}$, so $x_{-}x_{+} < 1$.

Transfer $z$ dollars from asset 2 to asset 1, followed by $z$ from asset 1 to asset 2, in two nonoverlapping active periods of dollar rate one. The exact individual dollar ledgers close after the second period, and the path belongs to $\mathsf{C}_{1}$. Starting at $x_{i} = 1$, the first-period prices remain between $x_{-}$ and $x_{+}$. The reversed second-period seller flow converges uniformly toward $x_{-}$ for initial states in $\left\lbrack 1,x_{+} \right\rbrack$, while the buyer flow converges uniformly toward $x_{+}$ for initial states in $\left\lbrack x_{-},1 \right\rbrack$. This follows by scalar comparison with the respective flows starting at the extreme endpoints of those compact intervals. Therefore, as $z \rightarrow \infty$,

$$\left( x_{1}(2z),x_{2}(2z) \right) \rightarrow \left( x_{-},x_{+} \right),\quad\quad x_{1}(2z)x_{2}(2z) \rightarrow x_{-}x_{+} < 1.$$

Some finite $z$ consequently has negative mean terminal log return. For $N = 2$ and $\alpha = 1/2$, the maximum of the two losses is at least their mean, so $\mathcal{C}_{1/2} = \bar{L} = - \frac{1}{2}\log\left( x_{1}x_{2} \right) > 0$. Throughout the construction $x_{i} \geq x_{-} > 0$; hence $M = 2z$, $H_{i}^{-} \leq z/x_{-}$ and $r_{i}^{gross} \leq 1/x_{-}$ are all finite.

For the promised explicit witness take $p = 5/4$, $K = 1$ and $z = 4$. The strict rational fourth-power comparisons

$$(3/4)^{4} > 1/4,\quad(2/3)^{4} < 1/3,\quad(3/2)^{4} > 5/2$$

imply $1/4 < x_{-} < 1/3$ and $1 < x_{+} < 5/2$. The seller flow satisfies $f_{-}\prime(x) < - 1$, so during the second four-dollar period,

$$x_{1}(8) - x_{-} \leq e^{- 4}\left( x_{1}(4) - x_{-} \right) < \frac{5}{2}e^{- 4}.$$

The second-period buyer price remains below $x_{+} < 5/2$. Since the positive exponential series gives $e^{4} > \sum_{k = 0}^{5}4^{k}/k! = 643/15$, it follows that

$$x_{1}(8)x_{2}(8) < \frac{5}{2}\left( \frac{1}{3} + \frac{5}{2}\frac{15}{643} \right) = \frac{7555}{7716} < 1.$$

Both prices always exceed $x_{-} > 1/4$. Each asset sells exactly four dollars once, so its actual sale of shares is less than $4/(1/4) = 16$; the unit incident dollar rate gives $r_{i}^{gross} < 4$. Every asserted inequality in (4.2) is therefore exact and independent of ODE numerical integration. ◻

**Proposition 4.4** (The critical two-node exponent $p = 3/2$ is also reachable). *For* $N = 2$*,* $F = \eta = 1$*, any* $K > 0$ *and* $p = 3/2$*, there is a finite-dollar, terminally dollar-closed two-edge reversal in* $\mathsf{C}_{1}$ *with strictly positive* $\mathcal{C}_{1/2}(T)$*, finite actual seller-side inventory, and a finite gross share-execution rate.*

*Proof.* Use the scalar buyer/seller flows $x\prime = f_{\pm}(x)$ from Theorem 4.3, now with $r = p - 1 = 1/2$. Their stable positive equilibria satisfy $x_{-}x_{+} = 1$, because $f_{-}\left( 1/x_{+} \right) = 0$. The positive magnitudes of the linearized relaxation rates are

$$\gamma_{-} = - f_{-}\prime\left( x_{-} \right) = \frac{K}{2}\left( 1 + \frac{1}{x_{-}} \right),\quad\quad\gamma_{+} = - f_{+}\prime\left( x_{+} \right) = \frac{K}{2}\left( 1 + \frac{1}{x_{+}} \right).$$

Since $x_{-} < 1 < x_{+}$, one has $\gamma_{-} > \gamma_{+} > 0$.

Write $\phi_{\pm}(a;y)$ for the scalar flow of $x\prime = f_{\pm}(x)$ after executed-dollar activity $a$, started from $x(0) = y$. After the first of two opposite transfers of equal dollar amount $z$, the first asset is in $\left\lbrack 1,x_{+} \right\rbrack$ and the second in $\left\lbrack x_{-},1 \right\rbrack$. Scalar order preservation gives

$$\begin{matrix}
0 < \Delta_{-}(z){: =}x_{1}(2z) - x_{-} & \leq \phi_{-}\left( z;x_{+} \right) - x_{-} = :A(z), \\
0 < \Delta_{+}(z){: =}x_{+} - x_{2}(2z) & \geq x_{+} - \phi_{+}(z;1) = :B(z) > 0.
\end{matrix}$$

For a scalar $C^{1}$ flow approaching a hyperbolic stable equilibrium $x_{*}$ with $f\prime\left( x_{*} \right) = - \gamma$, the logarithmic derivative of the positive distance to equilibrium tends to $- \gamma$. Integrating this logarithmic derivative and averaging over the elapsed activity interval proves

$$\lim_{a \rightarrow \infty}\frac{1}{a}\log\left| x(a) - x_{*} \right| = - \gamma.$$

Applying this result to $A(z)$ and $B(z)$ shows that $A(z)/B(z) \rightarrow 0$, because $\gamma_{-} > \gamma_{+}$. Hence $\Delta_{-}(z)/\Delta_{+}(z) \rightarrow 0$, and for all sufficiently large finite $z$,

$$x_{1}(2z)x_{2}(2z) - 1 = x_{+}\Delta_{-}(z) - x_{-}\Delta_{+}(z) - \Delta_{-}(z)\Delta_{+}(z) < 0.$$

Thus $\mathcal{C}_{1/2} = - \frac{1}{2}\log\left( x_{1}x_{2} \right) > 0$. The dollar ledgers close exactly, each asset's true seller shares do not exceed $z/x_{-}$, and unit dollar execution rate gives a finite gross share rate at most $1/x_{-}$. ◻

**Corollary 4.5** (Reachability extends strictly beyond $p = 3/2$). *For every fixed* $K > 0$ *there exists* $\varepsilon(K) \in (0,1/2)$ *such that, for every exponent* $3/2 \leq p < 3/2 + \varepsilon(K)$*, one and the same finite two-edge dollar amount* $z_{K} > 0$ *generates a terminally dollar-closed* $\mathsf{C}_{1}$ *path with* $\mathcal{C}_{1/2}\left( 2z_{K} \right) > 0$*. The paths have strictly positive prices, finite turnover* $M = 2z_{K}$*, genuine seller-side share inventories and finite gross share-execution rates under unit dollar-amount-per-time scheduling. No value of* $\varepsilon(K)$ *or sharp exponent threshold is asserted here.*

*Proof.* Fix $K > 0$. Proposition 4.4 provides a finite $z_{K}$ whose two consecutive oppositely directed transfers, each of dollar amount $z_{K}$, have terminal positive prices and strict product $x_{1}\left( 2z_{K} \right)x_{2}\left( 2z_{K} \right) < 1$ at $p = 3/2$. The entire reference trajectory is positive and continuous on the compact amount interval $\left\lbrack 0,2z_{K} \right\rbrack$, and therefore has a positive minimum price. On a compact positive neighborhood of this reference path, the two scalar edge-flow vector fields

$$f_{\pm}(x;p) = \pm x^{p - 1} - K(x - 1)$$

are continuously differentiable in $(x,p)$. Standard continuous dependence of ODE solutions on parameters, applied successively to both fixed-dollar stages, implies uniform convergence of the trajectories and convergence of their terminal-price products as $p \rightarrow 3/2$. The strict terminal product inequality persists throughout some one-sided interval $\lbrack 3/2,3/2 + \varepsilon(K))$. After narrowing that interval if needed, every price along the two events exceeds half the positive minimum reference price. Thus true seller-side share consumptions and gross share-execution rates are finite, uniformly in $p$ on the stated interval. Both edges have the same fixed positive dollar mass and opposite directions, so the individual executed-dollar ledgers close exactly for all such $p$, and $\mathsf{C}_{1}$ holds at every active time. For two assets at $\alpha = 1/2$, a terminal price product below one gives positive $\mathcal{C}_{1/2}$, as required. ◻

#### The remaining two-node global boundary.

For $1 < p \leq 3/2$, Theorems 4.2, 4.3 and Proposition 4.4 establish a genuine turnover-dependent reachability transition; by Corollary 4.5, this positive region extends slightly above $p = 3/2$ for each fixed $K$: sufficiently small dollar-closed round trips are obstructed, yet an appropriate finite larger round trip succeeds. The global reachability question for the remaining $p \in \lbrack 3/2 + \varepsilon(K),2)$ is *not* classified by these results, and neither the minimum successful turnover nor the full $p,K,N$ and graph-topology phase diagram is claimed.

# 5. Floors, aggregate barriers and execution resources

**Theorem 5.1** (Scalar activity-driven price floors). *For the power response* $g_{p}$*, every individual normalized price is bounded from below by the largest root* $r \in (0,1)$ *of* $K(1 - r) = r^{p - 1}$ *whenever such a root exists. More precisely: (i) if* $p < 1$*, a strictly positive floor occurs for* $$K \geq K_{c}(p) = \frac{(2 - p)^{2 - p}}{(1 - p)^{1 - p}};$$ (5.1) *(ii) for* $p = 1$ *it occurs if* $K > 1$*, and equals* $1 - 1/K$*; (iii) for* $p > 1$ *it occurs for every* $K > 0$*. For* $p = 0$*,* $K_{c} = 4$ *and the upper root is* $r = \left( 1 + \sqrt{1 - 4/K} \right)/2$*.*

*Proof.* Using activity as clock and $|\, du/\, da| \leq 1$, the lowest possible drift in $(0,1)$ is $\, dx/\, da \geq K(1 - x) - x^{p - 1} = :f_{-}(x)$. A root of $f_{-}$ is a one-sided barrier by scalar comparison and local ODE uniqueness. For $p < 1$, minimize $x^{p - 1}/(1 - x)$ on $(0,1)$ to get (5.1), including the noncrossable double root at equality. For $p = 1$ solve the linear root equation. For $p > 1$, $f_{-}$ decreases strictly from $K$ at zero to $- 1$ at one and has a unique positive zero. ◻

**Theorem 5.2** (Necessary full-coverage bound). *For any finite-variation flow-completed control in* $\mathsf{C}_{0}$*,* $p < 2$ *and* $x_{i}(0) = 1$*,* $$\sum_{i = 1}^{N}x_{i}(t)^{2 - p} \geq 1.$$ (5.2) *In particular all* $N$ *prices cannot simultaneously be no larger than* $e^{- \delta}$ *unless* $\delta \leq \left( \log N \right)/(2 - p)$*.*

*Proof.* Put $\nu = 2 - p > 0$ and $H = \sum_{i}^{}w_{p}\left( x_{i} \right)$. At every state where $H \leq (1 - N)/\nu$, we have $\sum_{i}^{}x_{i}^{\nu} \leq 1$, whence every $x_{i} \leq 1$ and $\, dH = - K\sum_{i}^{}x_{i}^{1 - p}\left( x_{i} - 1 \right)\, da_{i} \geq 0$. Initially $H = 0 > (1 - N)/\nu$; continuity and the inward-pointing inequality forbid crossing below $(1 - N)/\nu$. The event-flow convention permits the same argument during every edge of a finite-variation path. Rearrangement gives (5.2). ◻

**Theorem 5.3** (Necessary resources). *Suppose at least* $k$ *assets end at* $S_{i}(T) \leq s = Fe^{- \delta} < F$*. Then for any* $\mathsf{C}_{0}$ *control,* $$M \geq k\left\lbrack - \Phi(s) \right\rbrack,\quad\quad\sum_{i}^{}H_{i}^{-} \geq k\left\lbrack - \Psi(s) \right\rbrack.$$ (5.3) *If* $X_{i}(T) = 0$ *and initial shares* $H_{i}$ *are available, then* $E\left( S_{i}(T) \right) \leq FH_{i}$*. If* $R(S) \leq R_{\max}$ *for all* $S \in \lbrack F,U\rbrack$ *and* $S_{i}(t) \leq U$ *throughout, a terminally dollar-closed asset ending below* $s$ *must have above-benchmark activity* $$\int_{S_{i} > F}^{}\, dA_{i} \geq \frac{- \Phi(s)}{\kappa R_{\max}}\quad\left( R_{\max} > 0 \right).$$ (5.4)

*Proof.* On the last downward excursion from $F$ to $s$, $\, d\Phi = \, dX - \kappa R\, dA \geq \, dX$ since $R < 0$ below $F$. Thus the negative-dollar variation of each target is at least $- \Phi(s)$; summing sellers counts each paired dollar transfer once. Similarly, a downward price excursion below $F$ satisfies $\, dS \geq - g(S)( - \, d\theta)_{+}$ and therefore requires at least $- \Psi(s)$ sold shares. Cost identity (2.9) and $\Delta\theta_{i} \geq - H_{i}$ give the inventory inequality. Finally, $- \Phi\left( S_{i}(T) \right) = \kappa\int R\, dA$ under dollar closure and its positive part can only arise above $F$; there $R \leq R_{\max}$. If $S_{i}(T) \leq s$, the stated bound follows. ◻

**Theorem 5.4** (A $K$-dependent turnover lower bound). *For* $p = 0$*, define* $D_{F} = F^{2}/\eta$*. If* $k$ *dollar-closed assets end at or below* $s = Fe^{- \delta}$*, then* $$M \geq kD_{F}\sqrt{\frac{1 - e^{- 2\delta}}{2K(2 + K)}}.$$ (5.5) *In particular this necessary lower bound diverges as* $K^{- 1/2}$ *when* $K \downarrow 0$ *at a fixed positive target severity.*

*Proof.* Normalize $F = \eta = 1$ and use the $i$th node's activity clock $a \in \lbrack 0,2b\rbrack$. Dollar closure makes its total buys and sells equal $b$, so its signed ledger obeys $u(0) = u(2b) = 0$ and $u(a) \leq \min(a,2b - a)$. For $w = \left( x^{2} - 1 \right)/2$ and $r = x(x - 1)$, $\, dw = \, du - Kr\, da$. Since $r \geq - 1/4$ and $r \leq 2\lbrack w\rbrack_{+}$ for every $x > 0$,

$$\left\lbrack w(a) \right\rbrack_{+} \leq \min(a,2b - a) + Ka/4,\quad\quad\int_{0}^{2b}r\, da \leq (2 + K)b^{2}.$$

At the terminal time, $- w(T) = K\int r\, da \geq \left( 1 - s^{2} \right)/2$. Hence $b \geq \sqrt{\left( 1 - s^{2} \right)/\left\lbrack 2K(2 + K) \right\rbrack}$. The sum of all dollar purchases equals paired turnover $M$. Restore the executed-dollar unit $D_{F}$. ◻

**Proposition 5.5** (All-node second-session obstruction). *If all assets stay at or below* $F$ *throughout a second trading session, they cannot all close that session strictly below their respective opening prices, regardless of execution-rate bounds.*

*Proof.* The activity potential obeys (2.8), and every $R\left( S_{i} \right) \leq 0$ throughout the session, hence $H$ cannot decrease. Strict decline of every price would strictly decrease $H = \sum_{i}^{}\Phi\left( S_{i} \right)$, a contradiction. ◻

# 6. Bounded gross share rates and local speed constraints

A rate bound changes the admissible set: specify the *gross* share rate, not the rate of the net executed-dollar ledger,

$$\frac{{\dot{A}}_{i}(t)}{S_{i}(t)} \leq v\quad\text{for almost every }t \in \lbrack 0,T\rbrack,\quad\quad v < \infty.$$ (6.1)

Writing $h(S) = g(S)/S$, the pairing condition $\sum_{i}^{}{\dot{X}}_{i} = 0$ cancels the first-order aggregate price response at the common benchmark. This cancellation is local and does not imply a conserved scalar over the full path. Whereas optimal-execution studies such as \[2\], \[16\] investigate how to choose trading rates under cost and speed constraints, our gross share-rate restriction is a *reachability* constraint: it rules out certain terminal losses without identifying an investor's optimal trading policy.

**Theorem 6.1** (Conditional quadratic small-rate barrier). *Let* $I = \lbrack F - d,F + d\rbrack \subset (0,\infty)$ *be a compact interval on which* $g$ *is positive and* $C^{2}$*. Define* $$C_{I} = \sup_{S \in I}\{ g(S) + \kappa S|S - F|\},\quad U_{I} = \sup I,\quad L_{I} = \sup_{S \in I}\left| h\prime(S) \right|.$$ *If* $vC_{I}T < d$*, every trajectory satisfying (6.1) remains in* $I$ *and* $$\left| \bar{S}(T) - F \right| \leq \frac{1}{2}v^{2}T^{2}C_{I}U_{I}\left( L_{I} + \kappa \right),\quad\mathcal{C}_{\alpha}(T) \leq \bar{L}(T) \leq B_{I}v^{2}T^{2},$$ (6.2) *where* $B_{I}$ *is the explicit constant obtained by combining the first bound with the Taylor inequality* $- \log(1 + y) \leq - y + y^{2}/\left\lbrack 2(1 - b)^{2} \right\rbrack$ *for* $|y| \leq b = vC_{I}T/F < 1$*. Thus a uniformly bounded-rate market cannot produce a fixed positive terminal crisis severity on an arbitrarily short, sufficiently regular horizon.*

*Proof.* The inequalities $\left| {\dot{X}}_{i} \right| \leq {\dot{A}}_{i} \leq vS_{i}$ imply $\left| {\dot{S}}_{i} \right| \leq vC_{I}$ as long as $S_{i} \in I$. A first-exit argument establishes invariance of $I$ under $vC_{I}T < d$. Let $y_{i} = S_{i} - F$. Summing the price equations and subtracting the common coefficient $h(F)$ from their trade terms gives

$$\dot{\bar{S}} = \frac{1}{N}\sum_{i}^{}\left\lbrack h\left( S_{i} \right) - h(F) \right\rbrack{\dot{X}}_{i} - \frac{\kappa}{N}\sum_{i}^{}\left( S_{i} - F \right){\dot{A}}_{i}.$$

Use $\left| y_{i}(t) \right| \leq vC_{I}t$, $\left| h\left( S_{i} \right) - h(F) \right| \leq L_{I}\left| y_{i} \right|$ and ${\dot{A}}_{i} \leq vU_{I}$ and integrate $t$ from $0$ to $T$. The logarithmic estimate and $\mathcal{C}_{\alpha} \leq \bar{L}$ complete the proof. The same conclusion holds for either $\mathsf{C}_{0}$ or $\mathsf{C}_{1}$ control, since gross activity was retained throughout. A rate-independent explicit constant under a fixed margin is given in Proposition B.1, and a matching local quadratic construction is supplied by Proposition B.2. ◻

**Proposition 6.2** (Pure-sale speed test). *Suppose the price falls from* $s_{0}$ *to* $s_{1} < s_{0}$ *during a period of length* $\tau$*, and the gross share rate is bounded by* $v$*. On a price interval where* $G_{-}(S) = g(S) + \kappa S(S - F) > 0$*, a necessary condition is* $$v\tau \geq \int_{s_{1}}^{s_{0}}\frac{dS}{G_{-}(S)}.$$ (6.3) *In the normalized* $p = 0,K = 2$ *model,* $G_{-}(x) = 2\left( x - \frac{1}{2} \right)^{2} + \frac{1}{2}$*, so the integral equals* $\arctan\left( 2s_{0} - 1 \right) - \arctan\left( 2s_{1} - 1 \right)$*.*

*Proof.* A sale is the maximal instantaneous negative net-dollar flow, ${\dot{X}}_{i} \geq - {\dot{A}}_{i}$. Thus $- {\dot{S}}_{i} \leq \left\lbrack g\left( S_{i} \right)/S_{i} + \kappa\left( S_{i} - F \right) \right\rbrack{\dot{A}}_{i} \leq vG_{-}\left( S_{i} \right)$ when $G_{-} > 0$. Integrate a decreasing segment. The result is a *necessary* scalar constraint; it does not construct paired-dollar counterparties or close their ledgers. ◻

#### A bounded-rate local construction.

Spread the nine-edge triangle of Theorem 3.1 over a fixed positive interval, assigning each edge its required dollar amount at a sufficiently small positive rate. The price path remains in a compact neighborhood of $F$, and each gross share rate is of order $z/T$ while its terminal losses are of order $z^{2}$. Thus the quadratic exponent in (6.2) is locally attainable for $N \geq 3$, though neither the constant nor any severe-loss optimal execution is inferred from this local scaling.

# 7. Rolling price limits, breadth, and market cuts

Suppose consecutive sessions are indexed by $d = 1,\ldots,D$. Within each session, a price may not move beyond a fraction $\ell \in (0,1)$ of its preceding close. Specifically, if $s_{i,d - 1}$ is the previous close, the entire session must satisfy $(1 - \ell)s_{i,d - 1} \leq S_{i}(t) \leq (1 + \ell)s_{i,d - 1}$. The next session's band is reset to the new close; the fundamental benchmark $F$ is *not* reset. This repeatedly resetting percentage band is a stylized mathematical constraint, not a claim about the detailed tick-based daily limits of any specific exchange. Real market schedules, including the domestic-equity rules documented by Japan Exchange Group \[13\], may be price-level dependent; the $\pm 25\%$ scenarios below are therefore hypothetical stress constraints.

**Proposition 7.1** (Exact cross-sectional compensation criterion). *Let* $k$ *named targets close at the same lower band ratio* $q = 1 - \ell$ *for* $D$ *consecutive sessions, so that* $S_{i}(T) = Fq^{D}$ *on that target set* $J$*. Put* $\lambda = - \log q$*. For a coverage level* $\alpha$ *with* $\lceil\alpha N\rceil \leq k$*,* $\mathcal{C}_{\alpha}(T) \geq \delta$ *is equivalent to* $$\delta \leq D\lambda\quad\text{and}\quad\prod_{j \notin J}^{}\frac{S_{j}(T)}{F} \leq \exp\{ kD\lambda - N\delta\}.$$ (7.1)

*Proof.* The $k$ targets imply $Q_{\alpha}(T) \geq D\lambda$. The average log loss is exactly

$$\bar{L}(T) = \frac{kD\lambda - \sum_{j \notin J}^{}\log\left( S_{j}(T)/F \right)}{N}.$$

Rearrange the inequality for its being at least $\delta$. ◻

**Proposition 7.2** (Cut receiving capacity under gross speed). *Under the rate cap (6.1), any nonempty proper asset subset* $J$ *obeys* $$\left| \sum_{i \in J}^{}{\dot{X}}_{i}(t) \right| \leq v\min\left\{ \sum_{i \in J}^{}S_{i}(t),\sum_{j \notin J}^{}S_{j}(t) \right\}$$ (7.2) *for almost every active time. Integrating this inequality gives a necessary duration/counterparty-capacity constraint for any proposed multiday target path.*

*Proof.* All transfers internal to $J$ cancel from its net dollar flow; only genuine cut edges contribute. The absolute net flow is at most the total gross cut activity on either side. Each side's gross amount is bounded by $v$ times its sum of contemporaneous prices. ◻

**Corollary 7.3** (All-asset repeated lower closes are impossible). *Suppose all* $N$ *assets start from their common benchmark* $F$*, and each session uses a rolling symmetric percentage band* $\left\lbrack (1 - \ell)s_{i,d - 1},(1 + \ell)s_{i,d - 1} \right\rbrack$ *with* $0 < \ell < 1$*. No admissible activity-driven path can make all assets close at the lower limit in both the first and second session, regardless of the turnover budget or whether* $\mathsf{C}_{0}$ *or* $\mathsf{C}_{1}$ *is used. Hence, for* $N = 10$ *and* $\ell = 1/4$*, the maximum number of assets that could have two successive lower-limit closes is at most nine; the certified Construction III establishes only the lower bound of five. The optimal number lies in* $\lbrack 5,9\rbrack$*.*

*Proof.* If every asset closes the first session at $(1 - \ell)F$, its permitted upper price throughout the second session is $(1 + \ell)(1 - \ell)F = \left( 1 - \ell^{2} \right)F < F$. Thus every asset stays below $F$ in that session. The activity potential $H = \sum_{i}^{}\Phi\left( S_{i} \right)$ is nondecreasing there, by (2.8), because $R\left( S_{i} \right) < 0$. All assets closing at the second lower limit would strictly decrease their prices from $(1 - \ell)F$ to $(1 - \ell)^{2}F$, strictly decreasing $H$, a contradiction. ◻

**Proposition 7.4** (A strict lower bound for repeated-limit gross share rates). *Fix the normalized* $p = 0$*,* $K = 2$ *activity-driven price law and the two sessions* $\lbrack 0,20\rbrack$ *and* $\lbrack 20,40\rbrack$*. If an asset closes successively at* $x(20) = 3/4$ *and* $x(40) = 9/16$*, while its gross share-execution rate satisfies* $\dot{A}(t)/x(t) \leq v$ *almost everywhere, then necessarily* $$v \geq v_{necessary}: = \frac{\arctan(1/2) - \arctan(1/8)}{20} > 0.0169.$$ (7.3) *Consequently the infimum* $v_{5}^{*}$ *over all valid ten-asset* $\mathsf{C}_{1}$ *executions with five such targets, exact terminal dollar closure and the same rolling bands, has the certified bracket* $$\frac{\arctan(1/2) - \arctan(1/8)}{20} \leq v_{5}^{*} < 0.133.$$ (7.4) *The upper bound uses Construction III and presumes its stated finite turnover and inventory resources are allowed. This is a nonsharp necessary-speed certificate, not an assertion that either bound is attained as the exact optimum.*

*Proof.* In the normalized constant-impact model the absolutely continuous activity dynamics satisfy

$$\dot{x} = \frac{\dot{u}}{x} - 2(x - 1)\dot{a},\quad\quad\left| \dot{u} \right| \leq \dot{a},\quad\quad\dot{a}/x \leq v.$$

Because $1 + 2x(x - 1) = 2(x - 1/2)^{2} + 1/2 > 0$ for every $x > 0$, scalar comparison gives

$$\dot{x} \geq - \frac{\dot{a}}{x}\left\lbrack 1 + 2x(x - 1) \right\rbrack \geq - v\left\lbrack 1 + 2x(x - 1) \right\rbrack.$$

With $\varphi(x) = \arctan(2x - 1)$ one has $\varphi\prime(x) = 1/\left\lbrack 1 + 2x(x - 1) \right\rbrack$; therefore $\frac{\, d}{\, dt}\varphi\left( x(t) \right) \geq - v$. Integrate over the second session:

$$\varphi(9/16) - \varphi(3/4) \geq - 20v.$$

Since $\varphi(3/4) = \arctan(1/2)$ and $\varphi(9/16) = \arctan(1/8)$, this proves the first bound. For a strictly rational verification of the displayed decimal lower bound, use the alternating-integrand inequality $1/\left( 1 + t^{2} \right) \geq 1 - t^{2} + t^{4} - t^{6}$ for $0 \leq t \leq 1/2$:

$$\arctan(1/2) - \arctan(1/8) = \int_{1/8}^{1/2}\frac{\, dt}{1 + t^{2}} \geq \frac{24890949}{73400320} > \frac{169}{500}.$$

Each of five named targets satisfies the same inequality. Construction III supplies one admissible five-target $\mathsf{C}_{1}$ path with strict maximum gross share rate below $0.133$, hence the stated upper bound on the infimum. ◻

The upper bound $N - 1$ is *not* shown to be attainable. In particular, no "at most seven repeated limits" conclusion transfers from the physical-time manuscript. The exact optimum between five and nine for ten assets remains open. Proposition 7.4 bounds the five-target minimum gross share rate strictly between an explicit positive necessary bound and $0.133$; its sharp value remains open. Propositions 7.2 and 6.2 are necessary tests only.

# 8. Three ten-asset constructions

We now normalize $F = \eta = 1$ and use the complete graph. A useful completion fact separates the design of a price path from the design of a paired transaction network.

**Lemma 8.1** (Equal-activity graph completion). *Let* $N \geq 2$*,* $a_{0} > 0$*,* $\sum_{i}^{}u_{i}(t) = 0$ *and* $\left| u_{i}(t) \right| \leq a_{0}$ *almost everywhere. In* $\mathsf{C}_{0}$ *there exist nonnegative edge-flow rates with* ${\dot{X}}_{i} = u_{i}(t)$ *and* ${\dot{A}}_{i} = a_{0}$ *for every* $i$*.*

*Proof.* Set desired node purchases $b_{i} = \left( a_{0} + u_{i} \right)/2$ and sales $s_{i} = \left( a_{0} - u_{i} \right)/2$. Their respective totals are $Na_{0}/2$. A seller $i$ can reach every buyer except itself, and the singleton Hall condition is $s_{i} + b_{i} = a_{0} \leq Na_{0}/2$. A group of at least two distinct sellers reaches every buyer, so every remaining max-flow/min-cut inequality holds. A nonnegative zero-diagonal transportation matrix therefore realizes the rates. ◻

**Lemma 8.2** (Continuous embedding with actual trade activity). *Let* $x_{i}(t) > 0$ *be an absolutely continuous trajectory satisfying* $\sum_{i}^{}x_{i}(t)\left\lbrack {\dot{x}}_{i}(t) + \rho\left( x_{i}(t) - 1 \right) \right\rbrack = 0$ *and* $\left| u_{i}(t) \right| \leq a_{0}$*, where* $u_{i} = x_{i}\left\lbrack {\dot{x}}_{i} + \rho\left( x_{i} - 1 \right) \right\rbrack$ *and* $\rho > 0$*. Then under* $p = 0$*,* $K = \rho/a_{0}$ *and controls in* $\mathsf{C}_{0}$*,* $x_{i}$ *solves the new activity system with exactly* ${\dot{A}}_{i} = a_{0}$ *and* ${\dot{X}}_{i} = u_{i}$*.*

*Proof.* Apply Lemma 8.1; in the new equation ${\dot{x}}_{i} = u_{i}/x_{i} - K\left( x_{i} - 1 \right)a_{0} = u_{i}/x_{i} - \rho\left( x_{i} - 1 \right)$, identically. No free decay occurs: the last term is generated by the paired gross execution flow. The turnover is $Na_{0}T/2$. ◻

## 8.1. Construction I: exact ten-asset halving

**Theorem 8.3** (All ten prices exactly halve with finite resources). *Fix* $N = 10$*,* $p = 0$*, and normalized* $F = \eta = 1$*. There exists a strictly positive-price, absolutely continuous* $\mathsf{C}_{0}$ *control on the fixed horizon* $T = 40$*, with* $$\rho = \frac{2}{5},\quad\quad h = 10^{- 16},\quad\quad a_{0} = 10^{17},\quad\quad K = 4 \cdot 10^{- 18},$$ (8.1) *for which* $X_{i}(T) = 0$ *and* $x_{i}(T) = 1/2$ *for every* $i$*. It can be implemented with paired turnover* $M = 2 \cdot 10^{19}$ *and gross seller inventories* $H_{i}^{-} < 10^{20}$*. These constants certify an analytic alternative to the much smaller, only floating-point historical trial* $K = 1/75$*,* $M = 6000$*.*

*Proof.* Write $x_{i}(t) = R(t)\sqrt{Y_{i}(t)}$ with $\sum_{i}^{}Y_{i} \equiv 1$ and $\dot{R} = \rho\left( \sum_{i}^{}\sqrt{Y_{i}} - R \right)$, $R(0) = \sqrt{10}$. Use ten successive role stages, in which each target once takes the high direction $a = \sqrt{1 - 9b^{2}}$ and otherwise takes a common low direction $b$, for $b \in \lbrack.06,.07\rbrack$. Set the initial and terminal direction to the uniform vector. The sharp-stage radial solution is $R_{b}(t) = H_{b} + \left( \sqrt{10} - H_{b} \right)e^{- \rho t}$, $H_{b} = a + 9b$. The terminal-radius residual $E(b) = R_{b}(40)/\sqrt{10} - 1/2$ has rigorously bracketed signs $E(.06) < - .018$ and $E(.07) > .001$. The high-minus-low ledger weight $W_{b}(t) = \psi\left( aR_{b}(t) \right) - \psi\left( bR_{b}(t) \right)$, with $\psi(z) = z(z - 1)$, is greater than $.7$ on the full parameter interval. Equal-$W_{b}$ stage integrals therefore make all ten sharp target ledgers equal; the nine moving-cut Jacobian has the exact discrete Green inverse estimate $\parallel J_{0}^{- 1} \parallel_{\infty} < 45$.

Replace every limiting jump by a width-$h$ interpolation linear in $Y$, including the two endpoint ramps. The node-ledger error is less than $2800h$ and each cut derivative differs from its sharp value by less than $200h$; these estimates are uniform on radius $r = 10^{- 6}$ neighborhoods of the equal-weight cut times. The map $t \mapsto t - J_{0}^{- 1}D^{h}(b,t)$ contracts each such ball with derivative norm below $1/4$ and center displacement below $r/2$. Thus every $b$ admits unique exact equal-ledger cuts. Their terminal-radius residual retains the strict endpoint signs, so the intermediate value theorem selects $b^{*}$ with $R_{h}(T) = \sqrt{10}/2$. Equality of all dollar ledgers and the paired-dollar identity $\sum_{i}^{}X_{i}(T) = 0$ give exact zero for all. The net dollar rates satisfy $\left| u_{i} \right| < 5/h + 8 < a_{0}$. Lemma 8.1 yields nonnegative no-self-edge paired flows with every node's gross dollar rate $a_{0}$. Since all prices exceed $.06$, each gross seller inventory is below $a_{0}T/.06 < 10^{20}$. Detailed constants and the correct $L^{1}$ moving-cut derivative appear in Appendix C. ◻

## 8.2. Construction II: nine targets, arbitrarily severe losses

**Theorem 8.4** (A fixed-resource all-severity family at 90% breadth). *For* $N = 10$*,* $p = 0$*, and* $F = \eta = 1$*, choose* $$\rho = 1,\quad T = 200,\quad h = 10^{- 16},\quad a_{0} = 10^{17},\quad K = 10^{- 17},\quad c = \frac{1}{100}.$$ (8.2) *For every* $\delta > 0$ *there exists an admissible* $\mathsf{C}_{0}$ *path on this same horizon and under the same model coefficients, with strictly positive prices and* $X_{i}(T) = 0$ *for all* $i$*, such that* $$\mathcal{C}_{0.9}(T) > \delta,\quad\quad M = 10^{20},\quad\quad H_{i}^{-} < 3 \cdot 10^{24}\quad(i = 1,\ldots,10).$$ (8.3) *These are analytic existence bounds rather than the historical floating-point trial with* $T = 4$*,* $h = .012$*,* $K = .002$ *and* $M = 10000$*; the latter remains numeric only.*

*Proof.* Set nine successive stage directions so that one of the nine targets has high component $a = \sqrt{1 - 8c^{2} - b^{2}}$ at a time, the other eight have the low component $c$, and the tenth compensator has component $b \in \left\lbrack 10^{- 5},.05 \right\rbrack$. The final direction assigns component $q \in (0,.01\rbrack$ to each target and $\sqrt{1 - 9q^{2}}$ to the compensator. The sharp radial solution is $R_{b}(t) = H_{b} + \left( \sqrt{10} - H_{b} \right)e^{- t}$, $H_{b} = a + 8c + b$. The compensator ledger

$$F_{q}(b) = \frac{R_{b}(T)^{2}\left( 1 - 9q^{2} \right) - 1}{2} + \int_{0}^{T}\psi\left( bR_{b}(t) \right)\, dt$$

has $F_{q}\left( 10^{- 5} \right) > .06$ and $F_{q}(.05) < - 3$ for *all* $0 \leq q \leq .01$. The high-minus-low weight $W_{b}(t) = \psi\left( aR_{b} \right) - \psi\left( cR_{b} \right) > .08$ makes every equal-weight nine-stage partition unique and supplies $\parallel J_{0}^{- 1} \parallel_{\infty} \leq 125$.

For $h = 10^{- 16}$, the node ledger differences from the sharp model are at most $72400h$ and cut derivatives differ by at most $1000h$, uniformly in $b,q$ and cut neighborhoods of radius $10^{- 6}$. The preconditioned cut-time contraction again has norm below $1/4$ and center displacement below $r/2$, so the nine target ledgers can be equalized with *exact*, ordered cut times for all $b,q$. The compensator's two endpoint signs survive; the intermediate value theorem closes its exact ledger. The other nine ledgers close by equality and paired-dollar accounting.

The radial comparison gives $1 \leq R \leq \sqrt{10} < 4$, so terminal target prices $x_{i}(T) = qR(T)$ tend to zero as $q \downarrow 0$. Since the compensator remains at a uniformly positive final price, the average and ninth-largest log losses both diverge. Every node has gross dollar activity rate $a_{0}$, realized by Lemma 8.1; hence the dollar turnover is fixed at $Na_{0}T/2 = 10^{20}$. Before the final $h$-window, every price exceeds $10^{- 5}$. During the final window the targets satisfy $x_{i}(t) \geq c\sqrt{1 - s}$ for $s \in \lbrack 0,1\rbrack$, so $\int_{T - h}^{T}dt/x_{i} \leq 2h/c$ uniformly in $q$. Consequently $H_{i}^{-} \leq a_{0}\left( T/10^{- 5} + 2h/c \right) < 3 \cdot 10^{24}$. The final windows are positive for all $q > 0$; the limiting $q = 0$ configuration is used only in the continuous bracketing argument, not as an admissible price path. ◻

**Theorem 8.5** (Uniform-resource severe partial coverage for fixed $p < 1$). *Fix* $N = 10$*,* $F = \eta = 1$*, and any fixed* $0 \leq p < 1$*. There exist constants* $T,K,M_{0},H_{0} \in (0,\infty)$*, depending on* $p$ *but independent of the desired severity* $\delta$*, such that for every* $\delta > 0$ *there is an absolutely continuous, strictly positive* $\mathsf{C}_{0}$ *execution on* $\lbrack 0,T\rbrack$ *with* $X_{i}(T) = 0$ *for all ten assets and* $$\mathcal{C}_{0.9}(T) > \delta,\quad\quad M \leq M_{0},\quad\quad H_{i}^{-} \leq H_{0}\quad(i = 1,\ldots,10).$$ (8.4) *Neither* $T$*,* $K$*, nor the budgets* $M_{0},H_{0}$ *depend on* $\delta$*. This theorem does not assert bounds uniform as* $p \uparrow 1$*, or a bounded pointwise gross-share rate as* $\delta \rightarrow \infty$*.*

*Proof.* Put $\nu = 2 - p > 1$, take equal gross dollar-activity rates $a_{0}$, and set $\rho = Ka_{0} = 1$. For the positive direction vector $Y$, write $x_{i} = RY_{i}^{1/\nu}$. The exact radial and ledger identities are (D.1)--(D.3). Take nine successive role stages, with each target high exactly once, all other targets low, and a fixed compensator component:

$$c = b_{+} = \frac{1}{100},\quad 0 < b < b_{+},\quad\quad a(b) = (1 - 8c^{\nu} - b^{\nu})^{1/\nu}.$$

The constant stage source is $H_{b} = a^{\nu - 1} + 8c^{\nu - 1} + b^{\nu - 1}$, independent of which target is high, and $R_{b}(t) = H_{b} + \left( 10^{1/\nu} - H_{b} \right)e^{- t}$. We have $aR_{b}(t) > 1 > cR_{b}(t)$ for all stages, so $W_{b}(t) = \psi_{\nu}\left( aR_{b} \right) - \psi_{\nu}\left( cR_{b} \right) > 0$, where $\psi_{\nu}(x) = x^{\nu - 1}(x - 1)$. Therefore the sharp nine-stage target-ledger differences have a unique ordered cut-time root by equal-$W_{b}$ partitions. Their Jacobian $J_{0} = L_{8}diag\left( W_{b}\left( t_{j} \right) \right)$ has strictly positive determinant, uniformly bounded inverse on a fixed positive compact interval for $b$.

At the formal endpoint $q = 0$ of the last target direction, the compensator ledger is positive at $b = 0$, while for the fixed $b_{+}$ it is negative for a sufficiently large *finite* choice of $T$. Choose such a $T$, then $b_{-} > 0$ small enough that these strict signs persist at $b_{-}$ and $b_{+}$, and then $q_{0} > 0$ sufficiently small to preserve them for all $q \in \left\lbrack 0,q_{0} \right\rbrack$. The detailed endpoint calculation is in Appendix D.

Use fixed-width affine transitions in the $Y$ coordinates, including one terminal ramp to target components $q^{\nu}$. The perturbation in the ledger differences and the cut-time Jacobian tends uniformly to zero as $h \downarrow 0$ on $b \in \left\lbrack b_{-},b_{+} \right\rbrack$, $q \in \left\lbrack 0,q_{0} \right\rbrack$. The moving-cut radial derivative is controlled in $L^{1}$, not pointwise, by (C.6); the direct interpolation variation converges to the sharp-stage integrand jump. Thus a *single* positive width $h$, independent of $q$, ensures exact ordered cut-time roots by a uniform contraction. The compensator endpoint signs survive that perturbation, so the intermediate value theorem chooses an exact $b = b(q)$ closing the compensator. The other nine dollar ledgers close by equalization and zero-sum paired accounting.

The fixed positive $h$ bounds all $\left| {\dot{u}}_{i} \right|$ independently of $q$; choose finite $a_{0}$ larger than that bound and put $K = 1/a_{0}$. The equal-activity completion lemma realizes the net rates on genuine nonnegative paired edges, with $M_{0} = 10a_{0}T/2$. Before the last ramp every target price is at least $c$; during that ramp its shares satisfy the uniform integrability bound (D.4), independent of $q$. The compensator stays above the positive lower bound $b_{-}$. Consequently a single finite $H_{0}$ covers every genuine seller-side share quantity.

Finally $1 \leq R(T) \leq 10^{1/\nu}$ and the nine targets end at $x_{i}(T) = qR(T)$. Their ninth-largest loss and the average log loss both tend to infinity as $q \downarrow 0$. Select $q > 0$ sufficiently small for the requested $\delta$. All executed trajectories have strictly positive prices; $q = 0$ was used only to isolate an endpoint root, not as an admissible execution. This completes the quantified construction. ◻

**Remark 8.6** (The distinction from the explicit $p = 0$ witness). *The fixed-resource result above holds for every fixed* $0 \leq p < 1$*, but its constants are allowed to depend strongly on* $p$ *and need not be numerically economical. The explicit* $h = 10^{- 16}$*,* $M = 10^{20}$ *and* $H_{i}^{-} < 3 \cdot 10^{24}$ *certificate of Theorem 8.4 remains a* $p = 0$*-specific alternative; it is not reused for a different exponent. The terminal inventory bound diverges as* $\nu \downarrow 1$*.*

## 8.3. Construction III: two lower-limit closes without instantaneous netting

**Theorem 8.7** (An internally certified $\mathsf{C}_{1}$ witness). *Take ten assets with* $p = 0$*,* $F = \eta = 1$*,* $K = 2$*, and sessions* $\lbrack 0,20\rbrack$ *and* $\lbrack 20,40\rbrack$*. There is an absolutely continuous* $\mathsf{C}_{1}$ *execution such that five targets close at* $3/4$ *and then at* $9/16$*, all assets obey sessionwise rolling* $\pm 25\%$ *bands, all dollar ledgers close at* $40$*, initial share inventory* $2$ *suffices for every asset, and* $$M < 11.261627 < 14,\quad\sup_{i,t}r_{i}^{gross}(t) < 0.133,\quad G(40) < 0.84,$$ (8.5) *where* $G = \left( \prod_{i}^{}x_{i} \right)^{1/10}$ *is the equal-weight geometric price index. Hence* $\mathcal{C}_{1/2}(40) > - \log(.84) > 0$ *and* $1 - G(40) > 16\%$*. The parameter and path inequalities are internally verified by outward-rounded interval arithmetic, subject to the implementation described in Appendix E; external certification is not claimed.*

*Proof.* Partition the ten assets into five disjoint target/compensator pairs $\left( x_{j},y_{j} \right)$. For $K = 2$, a pure buyer and pure seller satisfy

$$P_{+}\prime(s) = \frac{s}{1 - 2s(s - 1)},\quad\quad P_{-}\prime(s) = \frac{s}{1 + 2s(s - 1)}.$$ (8.6)

Both are strictly increasing on the price range used below. Buying $z$ dollars sends a price $x$ to the unique $x\prime$ satisfying $P_{+}(x\prime) - P_{+}(x) = z$; selling $z$ dollars sends $y$ to $y\prime$ with $P_{-}(y) - P_{-}(y\prime) = z$. These are the *complete* activity ODE flows, not pure-impact approximations.

In each pair use nine excursions: buy the target while selling the compensator to the common floor $c$, then (on the first eight excursions) sell the target to the prescribed rational lows

$$(1.085409,1.087707,1.085158,1.099042,1.106127,1.122661,1.14,1.15).$$ (8.7)

After the ninth purchase, sell each target to $3/4$ at the end of session 1; in session 2 sell it further to $9/16$ while the corresponding compensator buys. Every amount is determined uniquely by (8.6). Let $f(c)$ be the resulting signed target-dollar ledger. Directed interval evaluation gives

$$f(0.76065368494358) > 0 > f(0.76065368494359).$$ (8.8)

Because all inverse branches are continuous and strictly monotone, there is an exact $c_{*}$ in this bracket with $f\left( c_{*} \right) = 0$. The paired compensator ledger is then also zero.

In the remainder of session 2 sequentially execute the five compensator-only transfers $y_{1} \rightarrow y_{2} \rightarrow y_{3} \rightarrow y_{4} \rightarrow y_{5} \rightarrow y_{1}$, each of mass exactly $1/25 = 0.04$. This adds zero net dollars to every compensator and avoids opposite-direction flows at any instant. The certificate checks all 19 pair-segment endpoints and all five cycle transfers; monotonicity between endpoints extends the rolling-band bounds to the entire continuous path.

Let $A_{1},A_{2}$ be the dollar amounts per pair in sessions 1 and 2. Five disjoint pairs act in parallel at constant per-edge dollar rate $A_{1}/20$ in the first session. In the second, pair transfers followed by the five cycle edges are sequentially assigned the common active-edge rate $\left( A_{2} + 5/25 \right)/20$. Each session lasts exactly 20. The interval check yields $A_{1}/20/(3/4) < 0.133$ and $\left( A_{2} + 1/5 \right)/20/(9/16) < 0.133$. The conservative target inventory is $A/(2 \cdot 9/16) < 2$ where $A = A_{1} + A_{2}$; compensator inventory is bounded by $A/\left( 2c_{*} \right) + (1/25)/1.2 < 2$. Finally every compensator's terminal price is strictly below $1.23$, so $G^{2} < (9/16) \cdot 1.23 < {0.84}^{2}$. The interval proof details and reproducibility boundary appear in Appendix E. ◻

# 9. Numerical reconstruction and visual evidence

The figures in this section are recomputed for the activity-driven model. Figures based on historical floating-point reconstruction carry evidence level `NUMERIC_ONLY`: they are *diagnostics*, not interval certification. The exact alternative analytic constructions of Theorems 8.3 --8.4 have deliberately much larger resource bounds.

[Figure 1: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig01_trade_activity_not_conservation.pdf)

Figure 1. Paired executed-dollar transfers and positive gross activity. The activity-driven potential is not generally conserved. This replaces the old physical-time conservation diagram.

[Figure 2: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig02_powerlaw_log_response.pdf)

Figure 2. Power-law response and normalized log sensitivity in the new model. Curves illustrate scalar mechanisms; they do not constitute a complete global $(p,K,N)$ reachability phase diagram.

[Figure 3: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig03_I_ten_asset_float_paths.pdf)

Figure 3. Ten-asset half-price trajectory from the independent *floating-point* trial with $K = 1/75$, $T = 40$, $M = 6000$. The exact analytic witness of Theorem 8.3 uses different parameters and does not certify this plotted root.

[Figure 4: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig04_II_nine_target_float_paths.pdf)

Figure 4. Nine-target severe-loss trial using $T = 4$, $K = .002$, $M = 10000$, based on a floating-point reconstruction. Extreme $q$ inventory quadrature is not reported as precisely known.

Table 1. Guaranteed severity levels from the *analytic* family of Theorem 8.4. For each row take $q_{\delta} = e^{- 2\delta - 5} \leq 0.01$. These are exact existence bounds, *not* reconstructions of the floating-point trial roots.

  ----------------------------------------------------------------------------------------------------------------------------
  Target $\delta$   Terminal direction $q_{\delta}$   Guaranteed $\mathcal{C}_{0.9}(T)$   $M$            $\max_{i}H_{i}^{-}$
  ----------------- --------------------------------- ----------------------------------- -------------- ---------------------
  $3$               $e^{- 11}$                        \>3                                 $10^{20}$      \<3·10²⁴

  $5$               $e^{- 15}$                        \>5                                 $10^{20}$      \<3·10²⁴

  $10$              $e^{- 25}$                        \>10                                $10^{20}$      \<3·10²⁴

  $20$              $e^{- 45}$                        \>20                                $10^{20}$      \<3·10²⁴
  ----------------------------------------------------------------------------------------------------------------------------

  : Guaranteed severity levels from the analytic family of Theorem 8.4. For each row take q\_\\delta=e\^{-2\\delta-5}\\le0.01. These are exact existence bounds, not reconstructions of the floating-point trial roots.

The guarantee uses only $1 \leq R(T) < 4$ and $x_{i}(T) = q_{\delta}R(T)$ for nine targets: their log losses exceed $2\delta + 5 - \log 4$, while the compensator's log loss exceeds $- \log 4$. Hence

$$\mathcal{C}_{0.9}(T) \geq \min\left\{ 2\delta + 5 - \log 4,\,\frac{9\left( 2\delta + 5 - \log 4 \right) - \log 4}{10} \right\} > \delta.$$

This table restores the original severity-ladder question with a proved bound rather than claiming that an approximate trajectory attains a certified terminal price.

Table 2. Reconstruction of the old activity-model *numerical trials*. Numbers are floating-point estimates, not exact root certificates. The $q = 10^{- 8}$ share total is intentionally omitted because quadrature was not stable. This table is not the analytic severity menu in Table 1.

  ---------------------------------------------------------------------------------------------------------------
  Trial                $M$            $\mathcal{C}_{0.9}(T)$   Max ledger residual      Gross shares
  -------------------- -------------- ------------------------ ------------------------ -------------------------
  I, ten halves        $6000$         ---                      $1.03 \cdot 10^{- 9}$    $6724.54$ (max)

  II, $q = 10^{- 2}$   $10000$        $4.08329$                $2.16 \cdot 10^{- 10}$   $698769.15$ (max)

  II, $q = 10^{- 4}$   $10000$        $8.22846$                $2.16 \cdot 10^{- 10}$   $703402.95$ (max)

  II, $q = 10^{- 8}$   $10000$        $16.51777$               $1.25 \cdot 10^{- 10}$   not reliably integrated
  ---------------------------------------------------------------------------------------------------------------

  : Reconstruction of the old activity-model numerical trials. Numbers are floating-point estimates, not exact root certificates. The q=10\^{-8} share total is intentionally omitted because quadrature was not stable. This table is not the analytic severity menu in Table 1.

[Figure 5: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig05_III_C1_two_session_prices.pdf)

Figure 5. Two-session target and compensator prices for the $\mathsf{C}_{1}$ five-target construction. Root isolation and path bounds are derived from interval enclosures, not the pixels.

[Figure 6: original vector PDF](../../../../submission/v20-gate3-activity-recovery/figures/Fig06_III_C1_max_gross_share_rate.pdf)

Figure 6. Gross executed-share-rate schedule for the certified rolling-band construction. The per-node maximum is less than $.133$ in the specified time allocation.

# 10. Conditional robustness and heterogeneous quadratic response

The following two modifications of the base law are *separate models*. They are included to identify which structural barriers use homogeneous response and exactly paired execution. They are not silent extensions of the admissible control set in Definition 2.1.

**Proposition 10.1** (Unpaired forcing: continuous dependence and closure). *Consider the formal perturbation* $$\, dX_{i} = \sum_{e}^{}B_{ie}\,\, dz_{e} + e_{i}(t)\, dt,\quad\quad\, dA_{i} = \sum_{e}^{}\left| B_{ie} \right|\,\, dz_{e},\quad\quad e_{i} \in L^{1}(0,T).$$ (10.1) *The additional forcing is not itself counted as a real matched transaction or as gross executed-dollar activity. Let* $S^{e},S^{0}$ *be solutions with the same nonnegative paired-edge flows, parameters and initial prices, with* $e$ *and* $0$ *respectively. Suppose both paths stay in a common positive compact price interval* $I = \lbrack m,U\rbrack$*. Put* $y = \Phi(S)$ *and let* $L$ *be a Lipschitz constant of* $R \circ \Phi^{- 1}$ *on* $\Phi(I)$*, and* $G = \sup_{S \in I}g(S)/S$*. Then* $$\begin{matrix}
\sup_{0 \leq t \leq T}\left| y_{i}^{e}(t) - y_{i}^{0}(t) \right| & \leq e^{\kappa LA_{i}(T)}\, \parallel e_{i} \parallel_{L^{1}(0,T)}, \\
\sup_{0 \leq t \leq T}\left| S_{i}^{e}(t) - S_{i}^{0}(t) \right| & \leq Ge^{\kappa LA_{i}(T)}\, \parallel e_{i} \parallel_{L^{1}(0,T)}.
\end{matrix}$$ (10.2, 10.3) *In particular, for each* $\alpha \in (0,1\rbrack$*,* $$\left| \mathcal{C}_{\alpha}^{e}(T) - \mathcal{C}_{\alpha}^{0}(T) \right| \leq \frac{G}{m}\max_{i}\left\lbrack e^{\kappa LA_{i}(T)} \parallel e_{i} \parallel_{L^{1}(0,T)} \right\rbrack.$$ (10.4) *If the baseline ledger is terminally closed and* $\int_{0}^{T}e_{i}(t)\, dt = 0$ *for each asset, the perturbed ledger is also terminally closed. In the absence of this separate zero-integral condition, terminal closure is not preserved in general.*

*Proof.* In the transformed coordinate, the paired flow term is identical for the two trajectories, and $\, d\left( y_{i}^{e} - y_{i}^{0} \right) = e_{i}(t)\, dt - \kappa\{ R\left( S_{i}^{e} \right) - R\left( S_{i}^{0} \right)\}\, dA_{i}$. Gronwall's inequality in the nonnegative activity measure gives the first estimate. Since $\left( \Phi^{- 1} \right)\prime(y) = g(S)/S \leq G$ on the stipulated strip, the second follows. The scalar loss function $S \mapsto \log(F/S)$ is $1/m$-Lipschitz on $I$. Its arithmetic mean and its $k$th-largest order statistic are each 1-Lipschitz in the sup norm of the vector of losses, as is their minimum. This proves (10.4). Finally, integrate (10.1): $X_{i}^{e}(T) - X_{i}^{0}(T) = \int_{0}^{T}e_{i}(t)\, dt$. ◻

**Proposition 10.2** (Heterogeneous quadratic response: exact weighted balance). *Fix a common fundamental level* $F > 0$*. At node* $i$ *let* $g_{i}(S) = \eta_{i}(S/F)^{2}$ *and* $\kappa_{i} > 0$*, with* $D_{i} = F^{2}/\eta_{i} > 0$ *and* $q_{i} = \log\left( S_{i}/F \right)$*. Use actual paired-dollar flows and the activity law (2.1), allowing* $\eta_{i}$ *and* $\kappa_{i}$ *to differ between assets. Then every flow-completed path satisfies the exact relations* $$\begin{matrix}
D_{i}\, dq_{i} & = \, dX_{i} - \kappa_{i}D_{i}\left( 1 - e^{- q_{i}} \right)\, dA_{i}, \\
\, d\left( \sum_{i}^{}D_{i}q_{i} \right) & = - \sum_{i}^{}\kappa_{i}D_{i}\left( 1 - e^{- q_{i}} \right)\, dA_{i}.
\end{matrix}$$ (10.5, 10.6) *More generally, for arbitrary fixed weights* $w_{i}$*,* $$\, d\left( \sum_{i}^{}w_{i}q_{i} \right) = \sum_{e}^{}\left( \frac{w_{b(e)}}{D_{b(e)}} - \frac{w_{s(e)}}{D_{s(e)}} \right)\, dz_{e} - \sum_{i}^{}w_{i}\kappa_{i}\left( 1 - e^{- q_{i}} \right)\, dA_{i}.$$ (10.7) *If a path is bounded above by* $S_{i}(t) \leq U_{i}$ *and* $A_{i}^{+} = \int_{S_{i} > F}^{}\, dA_{i}$*, set* $\chi_{i}^{+} = \left\lbrack 1 - F/U_{i} \right\rbrack_{+}$*. Then* $$\sum_{i}^{}D_{i}q_{i}(T) \geq - \sum_{i}^{}\kappa_{i}D_{i}\chi_{i}^{+}A_{i}^{+}.$$ (10.8) *Consequently, if all assets end below their benchmarks with* $q_{i}(T) \leq - \delta_{i}$ *and* $\delta_{i} \geq 0$*, a necessary condition is* $$\sum_{i}^{}D_{i}\delta_{i} \leq \sum_{i}^{}\kappa_{i}D_{i}\chi_{i}^{+}A_{i}^{+}.$$ (10.9) *The inequalities are necessary, and they do not certify an unweighted systemic crisis or a globally sharp turnover bound.*

*Proof.* For $g_{i}(S) = \eta_{i}(S/F)^{2}$, $\Phi_{i}(S) = D_{i}\log(S/F)$ and $R_{i}(S) = D_{i}(1 - F/S)$. Apply the chain rule to every completed edge and use $\sum_{i}^{}\, dX_{i} = 0$. Keeping the weighted incidence term rather than cancelling it gives (10.7). Where $S_{i} \leq F$, $1 - F/S_{i} \leq 0$, so these contributions are nonnegative in (10.6); where $S_{i} > F$ they are bounded above by $\chi_{i}^{+}$. This yields (10.8) and then (10.9). ◻

**Proposition 10.3** (A closed-dollar two-node quadratic counterexample). *Consider two assets in the heterogeneous quadratic model, with* $\kappa_{1}/D_{1} > \kappa_{2}/D_{2} > 0$*. Execute one dollar transfer of amount* $z$ *from asset* $2$ *to asset* $1$*, followed immediately in activity order by the reverse transfer of the same amount* $z$*. The completed-event trajectory belongs to* $\mathsf{C}_{1}$*, remains strictly positive for sufficiently small* $z > 0$*, and satisfies* $X_{1}(T) = X_{2}(T) = 0$*. Nevertheless* $$\overline{L}(T) = \frac{1}{2}\left( \frac{\kappa_{1}}{D_{1}} - \frac{\kappa_{2}}{D_{2}} \right)z^{2} + O\left( z^{3} \right) > 0,\quad\quad Q_{1/2}(T) > 0.$$ (10.10) *Thus* $\mathcal{C}_{1/2}(T) > 0$ *although both response elasticities equal two. This does not contradict the homogeneous common-clock barrier in Proposition 4.1; its common-parameter assumption is essential.*

*Proof.* During an edge of dollar amount $a$, with incidence sign $\sigma_{i} \in \{ - 1,1\}$, the log price satisfies

$$\frac{\, dq_{i}}{\, da} = \frac{\sigma_{i}}{D_{i}} - \kappa_{i}\left( 1 - e^{- q_{i}} \right).$$ (10.11)

The leading log-price path is the triangle $q_{i}^{(0)}(a) = \sigma_{i}a/D_{i}$ for $0 \leq a \leq z$ and $q_{i}^{(0)}(a) = \sigma_{i}(2z - a)/D_{i}$ for $z \leq a \leq 2z$. Its integral is $\sigma_{i}z^{2}/D_{i}$. Since $1 - e^{- q} = q + O\left( q^{2} \right)$ uniformly for $|q| = O(z)$, and $\int_{0}^{2z}\sigma_{i}\, da = 0$, integration of (10.11) gives $q_{i}(2z) = - \sigma_{i}\kappa_{i}z^{2}/D_{i} + O\left( z^{3} \right)$. Take $\sigma_{1} = + 1$, $\sigma_{2} = - 1$. The first log price is negative, the second positive, and their arithmetic mean is negative precisely under the assumed coefficient inequality. True gross seller-side share quantities are finite because the entire path stays in a compact positive neighborhood of $F$. ◻

The results in this section distinguish exact changes in the model from robustness within it. Formula (10.2) is a *conditional* comparison for fixed edge flows, not a control perturbation theorem preserving exact target prices. The heterogeneous weighted identity does not supply a new unweighted global phase diagram. In particular, the still-unclassified higher-exponent part of the homogeneous two-node phase diagram, sharp full-coverage severity, maximum repeated-limit breadth, and globally optimal execution rates remain open; the positive region established through and locally beyond $p = 3/2$ is given by Theorem 4.3, Proposition 4.4, and Corollary 4.5.

# 11. Interpretation and limitations

The activity clock breaks the trade-time conservation of $\sum_{i}^{}\Phi\left( S_{i} \right)$. Its rate is instead $- \kappa\sum_{i}^{}R\left( S_{i} \right)\, dA_{i}$; the sign depends on the placement of gross activity across price regions. The local triangular protocol is already available in $\mathsf{C}_{1}$, but the large existence constructions I--II exploit the broader $\mathsf{C}_{0}$ by assigning common activity even to nodes with small net dollar rates. Such churning is real executed dollar volume under the stipulated control rules, not a claim about rational investors' equilibrium behavior. The $\mathsf{C}_{1}$ two-session construction excludes instantaneous netting but uses many temporal direction reversals; prohibiting round trips altogether is a different admissibility restriction.

Proposition 10.3 shows that even the two-node quadratic-response obstruction is parameter-sensitive: heterogeneous activity-recovery coefficients permit a closed-dollar local systemic loss. Theorem 4.3 adds a complementary homogeneous result: throughout $1 < p \leq 3/2$, a finite turnover path achieves a two-node systemic loss despite the rigorous small-turnover barrier. The explicit $p = 5/4$ witness obeys the stricter $\mathsf{C}_{1}$ constraint and a finite gross share-rate cap. Corollary 4.5 additionally proves a nonempty reachable interval immediately above $p = 3/2$ for every fixed $K$. The global classification outside this demonstrated range remains open; none of these results introduces strategic trading incentives.

For $p < 1$ the scalar floor boundary $K_{c}(p)$ rules out unbounded severity at sufficiently large $K$, while Theorem 8.5 establishes a nonempty fixed-exponent existence region (with explicit $p = 0$ constants in Theorem 8.4). The intervening parameter range and sharp resource-efficient bounds remain open. Price-floor nonexistence alone is not a sufficiency theorem. The two-session witness establishes attainability for *five* targets. Corollary 7.3 rules out simultaneous repeated lower closes for all ten, so the attainable optimum is between five and nine. The former seven-target obstruction of the physical-time model is not transferred here.

## 11.1. Quantified but unresolved sharpness questions

The present analysis preserves three distinct optimization questions from the full research baseline. Their status is a proved two-sided bound or a necessary condition, not a numerical guess promoted to an optimum.

#### Full-coverage amplitude (A04).

For $N = 10$, $p = 0$, $F = \eta = 1$ and fixed $K_{0} = 4 \cdot 10^{- 18}$, define

$$\delta_{all}^{*}\left( K_{0} \right): = \sup_{\substack{\mathsf{C}_{0}\text{ positive execution} \\ X_{i}(T) = 0\ \forall i \\ M < \infty,\ H_{i}^{-} < \infty\ \forall i}}\min_{1 \leq i \leq 10}\log\left( 1/x_{i}(T) \right).$$

Construction I and the aggregate invariant (5.2) rigorously imply

$$\log 2 \leq \delta_{all}^{*}\left( K_{0} \right) \leq \frac{1}{2}\log 10.$$ (11.1)

No construction or exclusion sharpens this interval to an equality at present. In particular, a bound on the calendar horizon is not a bound on all-asset loss amplitude (Proposition 2.2).

#### Repeated-limit coverage (P10/R03).

For the ten-asset $p = 0$, $K = 2$, two-session $\pm 25\%$ problem in the broad admissible $\mathsf{C}_{1}$ class with finite turnover, gross rate and seller inventories, let $k_{*}^{band}$ be the largest feasible number of assets closing at both lower session limits. Construction III and Corollary 7.3 give

$$5 \leq k_{*}^{band} \leq 9.$$ (11.2)

If the five-target condition is prescribed instead, Proposition 7.4 gives the genuine gross share-speed bracket

$$\frac{\arctan(1/2) - \arctan(1/8)}{20} \leq v_{5}^{*} < 0.133.$$ (11.3)

The upper speed bound requires allowing the turnover and inventories of the existing five-target certificate. The full nine-target upper bound is not a claim that six, seven, eight or nine targets are constructible. No exact optimal speed is identified.

#### Remaining two-node and robust-control sectors (T03/R01/R02).

For each fixed $K > 0$ the proved two-node homogeneous reachability region contains all $1 < p \leq 3/2$ and some further interval $3/2 < p < 3/2 + \varepsilon(K)$. The proof does not establish the full reachable set within $3/2 + \varepsilon(K) \leq p < 2$, nor does it prove that reachability is monotone in $p$ or $K$. The heterogeneous construction changes the model parameters; it is not a continuation theorem for a fixed homogeneous market. Robustness estimates such as (10.4) hold only on a common positive compact price strip with explicitly controlled unmatched-dollar forcing, and do not imply global closed-loop robustness or optimality.

These genuinely unresolved questions are part of the scientific scope of this manuscript. None is used as a premise for the three ten-asset existence results or for an unqualified conclusion in the abstract.

# 12. Conclusion

In an idealized fixed-benchmark market where every dollar transfer is paired and every asset's terminal dollar ledger closes, gross trade activity can induce both price impact and resilience. Three-asset trading cycles yield local all-market losses, while scalar floors, aggregate barriers and necessary execution bounds restrict their scale. In the quadratic family, the exact heterogeneous weighted balance and a two-node round-trip counterexample delimit the homogeneous barrier. Exact analytic continuation establishes all-ten halving and, for each fixed $0 \leq p < 1$, a nine-target uniform-resource severity family; an independent internally certified ten-asset control achieves five repeated lower-limit closes with finite rate and strict sessionwise bands. These conclusions concern deterministic admissibility, not real-world crash probability or strategic profitability.

# A. One-sided bounded variation and true seller-side inventory

This appendix proves the low-price variation statement used in Theorem 5.3 without reusing the physical-time restoration estimates of the earlier model.

**Lemma A.1** (Low-price excursion and one-sided variation). *Let* $S_{i}:\lbrack 0,T\rbrack \rightarrow (0,\infty)$ *be a continuous, flow-completed, finite-variation price path with* $S_{i}(0) = F$*,* $\kappa > 0$ *and* $g > 0$*. Define the cumulative net share ledger* $\theta_{i}$ *by* $\, d\theta_{i} = \, dX_{i}/S_{i}$*, and let* ${Var}^{-}\left( Z;\lbrack 0,T\rbrack \right)$ *denote the negative Jordan variation of a continuous finite-variation path* $Z$*. Then* $$\begin{matrix}
\left\lbrack - \Phi\left( S_{i}(T) \right) \right\rbrack_{+} & \leq {Var}^{-}\left( X_{i};\lbrack 0,T\rbrack \right), \\
\left\lbrack - \Psi\left( S_{i}(T) \right) \right\rbrack_{+} & \leq {Var}^{-}\left( \theta_{i};\lbrack 0,T\rbrack \right) \leq H_{i}^{-}.
\end{matrix}$$ (A.1, A.2) *In the broader control class* $\mathsf{C}_{0}$ *the final two quantities need not be equal; simultaneous genuine buys and sells increase gross shares even when net share flow cancels.*

*Proof.* The inequalities are void if $S_{i}(T) \geq F$. Otherwise let $t_{*} \in \lbrack 0,T)$ be the last time $S_{i}\left( t_{*} \right) = F$; continuity and $S_{i}(0) = F$ guarantee such a time. Then $S_{i}(t) < F$ for $t \in (t_{*},T\rbrack$. On this interval, $R\left( S_{i} \right) \leq 0$, hence

$$\, d\Phi\left( S_{i} \right) = \, dX_{i} - \kappa R\left( S_{i} \right)\, dA_{i} \geq \, dX_{i}.$$

Integration from $t_{*}$ to $T$ gives $X_{i}(T) - X_{i}\left( t_{*} \right) \leq \Phi\left( S_{i}(T) \right) < 0$, and the negative variation of $X_{i}$ dominates the absolute value of that negative net increment. Similarly, since $\Psi\prime(S) = 1/g(S)$,

$$\, d\Psi\left( S_{i} \right) = \, d\theta_{i} - \kappa\frac{S_{i} - F}{g\left( S_{i} \right)}\, dA_{i} \geq \, d\theta_{i}$$

on the same final excursion. This proves the first inequality in (A.2). On every event, the negative part of $\, d\theta_{i}$ is bounded by the sum of shares actually sold, $\sum_{e:B_{ie} = - 1}^{}\, dz_{e}/S_{i}$. Integrate this pointwise measure domination to obtain ${Var}^{-}\left( \theta_{i} \right) \leq H_{i}^{-}$. The reasoning also applies to arbitrary absolutely continuous simultaneous $\mathsf{C}_{0}$ edge flows; no invalid cancellation of gross trades was made. ◻

For a terminal price $S_{i}(T) \leq s < F$, monotonicity of $\Phi$ and $\Psi$ gives ${Var}^{-}\left( X_{i} \right) \geq - \Phi(s)$ and $H_{i}^{-} \geq - \Psi(s)$. Sum these bounds over any $k$ target assets. For the dollars, seller-side negative variation is bounded by actual seller-side dollar flow, which counts *each paired edge exactly once*. This produces (5.3); it is a necessary market-resource bound, not an existence statement.

# B. Gross-share execution rates: explicit bootstrap and a matching local order

The following proof gives a rate constant that does not depend on a selected small rate $v$, provided the local condition is formulated with a fixed strip margin. It also makes precise the claim of local quadratic order in $\mathsf{C}_{1}$.

**Proposition B.1** (Uniform small-rate bound with a fixed strip). *Let* $I = \lbrack F - d,F + d\rbrack$ *with* $0 < d < F$*, and set* $h(S) = g(S)/S$ *and* $C_{I},U_{I},L_{I}$ *as in Theorem 6.1. If* $$vC_{I}T < \min\{ d,F/2\},$$ (B.1) *then every admissible paired execution satisfying* ${\dot{A}}_{i}/S_{i} \leq v$ *stays in* $I$ *and obeys the explicit bound* $$\mathcal{C}_{\alpha}(T) \leq \bar{L}(T) \leq \left\{ \frac{C_{I}U_{I}\left( L_{I} + \kappa \right)}{2F} + \frac{2C_{I}^{2}}{F^{2}} \right\} v^{2}T^{2}.$$ (B.2) *The constant in braces is independent of* $v,T$*, although it depends on the fixed price strip and response parameters.*

*Proof.* On any subinterval before the first exit from $I$,

$$\left| {\dot{S}}_{i} \right| \leq h\left( S_{i} \right)\left| {\dot{X}}_{i} \right| + \kappa\left| S_{i} - F \right|{\dot{A}}_{i} \leq v\{ g\left( S_{i} \right) + \kappa S_{i}\left| S_{i} - F \right|\} \leq vC_{I}.$$

Thus $\left| S_{i}(t) - F \right| \leq vC_{I}t < d$, excluding a first exit. Let $y_{i} = S_{i} - F$. Since $\sum_{i}^{}{\dot{X}}_{i} = 0$ and $\left| {\dot{X}}_{i} \right| \leq {\dot{A}}_{i} \leq vU_{I}$,

$$\left| \frac{\, d}{\, dt}\bar{S}(t) \right| \leq \frac{1}{N}\sum_{i}^{}\left\{ L_{I}\left| y_{i} \right|\,\left| {\dot{X}}_{i} \right| + \kappa\left| y_{i} \right|{\dot{A}}_{i} \right\} \leq v^{2}C_{I}U_{I}\left( L_{I} + \kappa \right)t.$$

After integration, $\left| \bar{S}(T) - F \right| \leq \frac{1}{2}v^{2}T^{2}C_{I}U_{I}\left( L_{I} + \kappa \right)$. For $|w| \leq \frac{1}{2}$, Taylor's inequality $- \log(1 + w) \leq - w + 2w^{2}$ gives, with $w_{i} = y_{i}/F$,

$$\bar{L}(T) \leq - \frac{\bar{S}(T) - F}{F} + \frac{2}{NF^{2}}\sum_{i}^{}y_{i}(T)^{2}.$$

The already proved $\left| y_{i}(T) \right| \leq vC_{I}T < F/2$ then yields (B.2). ◻

**Proposition B.2** (Time-resolved $\mathsf{C}_{1}$ triangle attains quadratic order). *Fix* $N \geq 3$*, a common positive* $C^{2}$ *response* $g$*, and* $\kappa > 0$*. There are constants* $\varepsilon,C_{1},C_{2} > 0$*, depending on* $N,F,g,\kappa$*, such that for every* $0 < vT < \varepsilon$ *one can construct a dollar-closed* $\mathsf{C}_{1}$ *path on* $\lbrack 0,T\rbrack$ *whose true gross share rate satisfies* $\sup_{i,t}{\dot{A}}_{i}/S_{i} \leq v$ *and whose terminal systemic loss obeys* $$\mathcal{C}_{1}(T) \geq C_{1}(vT)^{2} > 0,\quad\quad M \leq C_{2}vT.$$ (B.3) *Thus, for fixed* $N$ *and a small local rate--horizon product, the quadratic scaling exponent of Proposition B.1 cannot in general be improved to a higher power.*

*Proof.* Take the nine-edge triangle from Theorem 3.1 for nodes $(1,2,3)$. For $N > 3$, concatenate one triangle on $(1,2,j)$ for each $j = 4,\ldots,N$; for $N = 3$ use only the first triangle. Let $m = 9\max\{ 1,N - 2\}$ be the total number of edges and assign each edge a dollar amount $z > 0$ and a time interval of length $T/m$. Each active edge then has dollar rate $mz/T$, and only its buyer and seller have positive gross activity. For sufficiently small $z$, all prices stay within $\lbrack F/2,3F/2\rbrack$. Therefore the gross share rate is bounded by $2mz/(FT)$. Choose $z = FvT/(4m)$; the rate is at most $v/2$, with a strict margin for all sufficiently small $vT$. The nine-edge expansion establishes that at the end of each triangle its three participating nodes undergo a strictly negative transformed-price change of magnitude $\kappa z^{2}$ times a fixed positive response-dependent coefficient, with an $O\left( z^{3} \right)$ remainder. The triangles start at prices $F + O\left( z^{2} \right)$, so composition retains a negative $- c_{i}z^{2} + O\left( z^{3} \right)$ leading term at every node, with $c_{i} > 0$ depending on its number of triangle memberships. The mean terminal log loss and every individual log loss are therefore bounded below by $Cz^{2}$ for some fixed $C > 0$ once $z$ is sufficiently small. Thus $\mathcal{C}_{1} \geq Cz^{2} = C_{1}(vT)^{2}$. Every dollar edge is paired, no asset buys and sells at the same instant, and its incident amounts comprise equal purchases and sales over each completed triangle; all net-dollar ledgers close exactly. The paired turnover is $M = mz = (F/4)vT$. ◻

# C. Quantitative cut-root existence and constant-resource construction

This appendix records the derivatives and numerical inequalities supporting Theorems 8.3 and 8.4. They do *not* certify the cached floating-point roots.

## C.1. Exact activity-driven radial identity

Let $Y_{i}(t) > 0$, $\sum_{i}^{}Y_{i}(t) = 1$, and $x_{i} = R\sqrt{Y_{i}}$. If

$$R\prime = \rho\left( H(Y) - R \right),\quad H(Y) = \sum_{i}^{}\sqrt{Y_{i}},\quad R(0) = \sqrt{10},$$ (C.1)

and

$$u_{i} = \frac{R^{2}}{2}Y_{i}\prime + \rho R\left( H(Y)Y_{i} - \sqrt{Y_{i}} \right),$$ (C.2)

then $\sum_{i}^{}u_{i} = 0$ and ${\dot{x}}_{i} = u_{i}/x_{i} - \rho\left( x_{i} - 1 \right)$. Taking equal constant gross dollar activity ${\dot{a}}_{i} = a_{0}$, $K = \rho/a_{0}$, makes these the original *activity-driven* dynamics, not an external time-decay approximation. Chain rule gives the exact terminal ledger, with $\psi(z) = z(z - 1)$,

$$X_{i}(T) = \frac{R(T)^{2}Y_{i}(T) - 1}{2} + \rho\int_{0}^{T}\psi\left( R(t)\sqrt{Y_{i}(t)} \right)\, dt.$$ (C.3)

Since $1 \leq H(Y) \leq \sqrt{10}$, the solution to (C.1) satisfies $1 \leq R \leq \sqrt{10}$.

## C.2. Exact Green inverse for cut times

On each of $m$ constant-direction role stages, the radial source $H_{b}$ is the same because the role directions differ by permutation only. Write $A_{j} = \int_{t_{j - 1}}^{t_{j}}W_{b}(t)dt$, where $W_{b}$ is the positive high-minus-low ledger integrand. Equating adjacent account ledgers yields $D_{j} = \rho\left( A_{j} - A_{j + 1} \right) = 0$ for $j = 1,\ldots,m - 1$. The sharp Jacobian is

$$J_{0} = \rho L_{m - 1}diag\left( W_{b}\left( t_{1} \right),\ldots,W_{b}\left( t_{m - 1} \right) \right),$$ (C.4)

with $L_{n}$ the Dirichlet tridiagonal matrix $2, - 1, - 1$. Its inverse admits an *exact* discrete Green kernel:

$$\left( L_{m - 1}^{- 1} \right)_{ij} = \frac{\min(i,j)\left( m - \max(i,j) \right)}{m},\quad\quad \parallel L_{m - 1}^{- 1} \parallel_{\infty} = \max_{i}\frac{i(m - i)}{2}.$$

Consequently the inverse norms are $25/2$ for ten stages and $10$ for nine. If $W_{b} \geq w_{*} > 0$, then $\parallel J_{0}^{- 1} \parallel_{\infty} \leq \parallel L^{- 1} \parallel_{\infty}/\left( \rho w_{*} \right)$, and $\det J_{0} = m\rho^{m - 1}\prod_{j}^{}W_{b}\left( t_{j} \right) > 0$. This is a quantitative nondegeneracy certificate; it does not assert that a double-precision cut vector is a mathematical root.

## C.3. Moving ramps: correct $L^{1}$, not $L^{\infty}$, derivative

Take an interior $h$-wide affine $Y$-ramp centered at a cut $\tau$. The two flanking role stages have the *same* source $H_{b}$, and the ramp contributes a compact pulse $\Delta_{h}(t;\tau) = d_{b}\left( (t - \tau)/h \right)$ with $\Delta_{h} = 0$ at both endpoints and $\left| \Delta_{h} \right| \leq D_{*} \leq 4$. Differentiation of the radial variation-of-constants formula followed by integration by parts gives the exact identity

$$\partial_{\tau}R_{h}(t) = - \rho\Delta_{h}(t;\tau) + \rho^{2}\int_{0}^{t}e^{- \rho(t - s)}\Delta_{h}(s;\tau)ds.$$ (C.5)

The right-hand side is $O(1)$ *inside* the ramp, so a pointwise global $O(h)$ derivative estimate would be false. However, Tonelli's theorem yields

$$\parallel \partial_{\tau}R_{h} \parallel_{L^{1}(0,T)} \leq 2\rho D_{*}h,\quad\quad\left| \partial_{\tau}R_{h}(T) \right| \leq \rho^{2}D_{*}h.$$ (C.6)

The integrand in (C.3) has bounded radial derivative $\left| \partial_{R}\psi\left( R\sqrt{Y_{i}} \right) \right| \leq 9$. The integrated radial part of the cut derivative is therefore $O(h)$. The direct interpolation derivative converges to the jump between adjacent sharp-stage integrands, uniformly over compact positive internal direction parameters. The end ramps are stationary when interior cuts vary. In Construction II the terminal direction $q \downarrow 0$ is included only as a continuous endpoint parameter, never differentiated with respect to $q$ at zero.

## C.4. Explicit contraction and sign bounds

Choose $h = 10^{- 16}$, a cut-neighborhood radius $r = 10^{- 6}$ and $a_{0} = 10^{17}$. For Construction I, the compact parameter interval $b \in \lbrack 3/50,7/100\rbrack$ has $W_{b} > .7$ and ten sharp stage gaps larger than $14/65$. The endpoint residual $R_{b}(40)/\sqrt{10} - 1/2$ is below $- .018$ on the left and above $.001$ on the right. There are eleven smoothing windows; from their total length and $1 \leq R \leq \sqrt{10}$,

$$\parallel R_{h} - R_{b} \parallel_{\infty} < 18h,\quad\max_{i}\left| X_{i}^{h} - X_{i}^{0} \right| < 2800h,\quad\max_{i,j}\left| \partial_{t_{j}}X_{i}^{h} - \partial_{t_{j}}X_{i}^{0} \right| < 200h.$$

The $\infty$-norm Jacobian preconditioner is below $45$, so the contraction norm is smaller than $45\left\lbrack (2/5)400r + 3600h \right\rbrack < 1/4$ and center displacement is below $45(2 \cdot 2800h) < r/2$. The resulting exact cut roots preserve the endpoint signs.

For Construction II, take $b \in \left\lbrack 10^{- 5},.05 \right\rbrack$, $c = .01$, $T = 200$. The sharp compensator ledger is greater than $.06$ at the left endpoint and less than $- 3$ at the right for all $0 \leq q \leq .01$. The weight satisfies $W_{b} > .08$ and nine stage gaps exceed $16/117$. The ten smoothing windows give

$$\parallel R_{h} - R_{b} \parallel_{\infty} \leq 40h,\quad\max_{i}\left| X_{i}^{h} - X_{i}^{0} \right| \leq 72400h,\quad\max_{i,j}\left| \partial_{t_{j}}X_{i}^{h} - \partial_{t_{j}}X_{i}^{0} \right| < 1000h.$$

With $\parallel J_{0}^{- 1} \parallel_{\infty} \leq 125$, the contraction norm is $125(400r + 16000h) < 1/4$ and the center displacement is $125(2 \cdot 72400h) < r/2$. These statements apply *uniformly in* $q$, with one fixed strictly positive $h$. The exact rational inequalities, including square-root and exponential brackets, are also checked by the independent `certify_gate2_explicit.py` diagnostic; the script is not a substitute for the analytic derivation.

## C.5. Edge completion, finite turnover, and true gross inventories

Equation (C.2) implies $\left| u_{i} \right| \leq 5/h + 8$ for I and $\left| u_{i} \right| \leq 5/h + 20$ for II, which are both below $a_{0} = 10^{17}$. At each instant prescribe purchases $b_{i} = \left( a_{0} + u_{i} \right)/2$ and sales $s_{i} = \left( a_{0} - u_{i} \right)/2$. The complete directed graph without self-edges admits a nonnegative transportation matrix from the sellers to the buyers because total supplies and demands both equal $Na_{0}/2$ and every singleton satisfies $b_{i} + s_{i} = a_{0} \leq Na_{0}/2$. Thus $A_{i}\prime = a_{0}$, $X_{i}\prime = u_{i}$ and $M = Na_{0}T/2$, *with real gross opposite flows* in $\mathsf{C}_{0}$ rather than a fictitious "activity clock." In I, every price remains above $.06$, giving $H_{i}^{-} < a_{0}T/.06 < 10^{20}$. In II, before the final ramp every price is at least $10^{- 5}$; on the last ramp target prices are at least $c\sqrt{1 - s}$ for $0 \leq s \leq 1$. Therefore $\int_{T - h}^{T}dt/x_{i} \leq 2h/c$, independent of $q > 0$; this leads to $H_{i}^{-} < 3 \cdot 10^{24}$. No fixed *pointwise* share-rate cap is claimed for II as $q \downarrow 0$.

# D. The sublinear-exponent radial representation and its uniform inventory lemma

This section makes explicit the scope of the fixed $p < 1$ research extension. It establishes the change of variables and the *resource integrability* at a terminal zero-direction limit, but the sharp-cut bracketing and Jacobian estimates are proved below for each fixed exponent; the $p = 0$ certificate is not a universal numerical certificate in $p$.

**Lemma D.1** (Exact radial identities for $0 \leq p < 1$). *Let* $\nu = 2 - p > 1$*, normalize* $F = \eta = 1$*, and prescribe identical gross dollar-activity rates* ${\dot{a}}_{i} = a_{0}$ *with* $\rho = Ka_{0}$*. For a continuously differentiable path of strictly positive directions* $Y_{i}(t)$ *with* $\sum_{i}^{}Y_{i} = 1$*, set* $x_{i} = RY_{i}^{1/\nu}$*. Then the paired-dollar balance* $\sum_{i}^{}{\dot{u}}_{i} = 0$ *holds precisely when* $$R\prime = \rho\{ H_{\nu}(Y) - R\},\quad\quad H_{\nu}(Y) = \sum_{i}^{}Y_{i}^{(\nu - 1)/\nu}.$$ (D.1) *For that radial solution the required net-dollar rates are* $${\dot{u}}_{i} = \frac{R^{\nu}}{\nu}{\dot{Y}}_{i} + \rho R^{\nu - 1}\left\{ H_{\nu}(Y)Y_{i} - Y_{i}^{(\nu - 1)/\nu} \right\},$$ (D.2) *and each terminal ledger satisfies* $$u_{i}(T) = \frac{x_{i}(T)^{\nu} - 1}{\nu} + \rho\int_{0}^{T}x_{i}(t)^{\nu - 1}\{ x_{i}(t) - 1\}\, dt.$$ (D.3) *In particular, with* $R(0) = N^{1/\nu}$ *and* $Y_{i}(0) = 1/N$*, the radial solution remains in the strip* $1 \leq R(t) \leq N^{1/\nu}$*.*

*Proof.* Differentiation of $x_{i}^{\nu}$ in the normalized activity law gives $\frac{1}{\nu}\frac{d}{dt}x_{i}^{\nu} = {\dot{u}}_{i} - \rho x_{i}^{\nu - 1}\left( x_{i} - 1 \right)$. Sum over all assets and use the zero-sum net-dollar rates. Since $\sum_{i}^{}x_{i}^{\nu} = R^{\nu}$ and $\sum_{i}^{}x_{i}^{\nu - 1} = R^{\nu - 1}H_{\nu}(Y)$, the equation for $R$ follows. Solving the individual identity for ${\dot{u}}_{i}$ and substituting (D.1) yields (D.2); its components sum to zero. Integration gives (D.3), since $u_{i}(0) = 0$ and $x_{i}(0) = 1$. Finally, Holder's inequality and concavity give $1 \leq H_{\nu}(Y) \leq N^{1/\nu}$ for $Y_{i} \geq 0$ on the simplex. Scalar comparison proves the asserted radial bounds. ◻

**Lemma D.2** (Uniform terminal share integrability). *Suppose that on a final window* $\lbrack T - h,T\rbrack$*, with* $0 < h < \infty$ *fixed, each target direction follows an affine path from a positive fraction at least* $c^{\nu}$ *to a terminal fraction* $q^{\nu}$*, where* $c > 0$ *and* $0 < q < c$*. Put* $s = (t - T + h)/h \in \lbrack 0,1\rbrack$*. Then* $$Y_{i}(t) \geq c^{\nu}(1 - s),\quad\quad x_{i}(t) \geq c(1 - s)^{1/\nu},\quad\quad\int_{T - h}^{T}\frac{\, dt}{x_{i}(t)} \leq \frac{h\nu}{c(\nu - 1)}.$$ (D.4) *This bound is independent of* $q$*. For equal gross dollar rate* $a_{0}$*, the true gross sale inventory consumed by any such target on the final window is at most* $a_{0}h\nu/\left\lbrack c(\nu - 1) \right\rbrack$*. The bound diverges as* $\nu \downarrow 1$ *(equivalently* $p \uparrow 1$*).*

*Proof.* Affineness gives $Y_{i} = (1 - s)Y_{i}(T - h) + sq^{\nu} \geq (1 - s)c^{\nu}$. The radial solution in Lemma D.1 is at least one, hence the price inequality follows. Integrate $\int_{0}^{1}(1 - s)^{- 1/\nu}\, ds = \nu/(\nu - 1)$ and use the gross sale rate bound ${\dot{A}}_{i}^{-}/x_{i} \leq a_{0}/x_{i}$. ◻

## D.1. Strict endpoint signs and a compact role-stage root

We give the endpoint construction used in Theorem 8.5. Fix $\nu \in (1,2\rbrack$, $\rho = 1$, $c = b_{+} = 1/100$, and for $b \in \left\lbrack 0,b_{+} \right\rbrack$ define

$$a(b) = \left( 1 - 8c^{\nu} - b^{\nu} \right)^{1/\nu},\quad\quad H_{b} = a(b)^{\nu - 1} + 8c^{\nu - 1} + b^{\nu - 1},\quad\quad R_{b}(t) = H_{b} + \left( 10^{1/\nu} - H_{b} \right)e^{- t}.$$

Since $\nu > 1$, $9c^{\nu} \leq 9c < 1$, so $a > c,b$. Moreover, $aR_{b}(0) > 1$, because $10a^{\nu} = 10\left( 1 - 8c^{\nu} - b^{\nu} \right) \geq 9.1 > 1$. At the other endpoint of the radial trajectory,

$$aH_{b} = a^{\nu} + 8ac^{\nu - 1} + ab^{\nu - 1} = 1 + 8c^{\nu - 1}(a - c) + b^{\nu - 1}(a - b) > 1.$$ (D.5)

Since $R_{b}$ lies between $10^{1/\nu}$ and $H_{b}$, $aR_{b}(t) > 1$ everywhere. Meanwhile $cR_{b}(t),bR_{b}(t) \leq c\, 10^{1/\nu} \leq 0.1 < 1$. Thus for the strictly positive high-minus-low ledger weight

$$W_{b}(t) = \psi_{\nu}\left( aR_{b}(t) \right) - \psi_{\nu}\left( cR_{b}(t) \right) > 0,\quad\quad\psi_{\nu}(x) = x^{\nu - 1}(x - 1),$$ (D.6)

the positivity is uniform on compact $b \in \left\lbrack b_{-},b_{+} \right\rbrack$ and $t \in \lbrack 0,T\rbrack$ for any $b_{-} > 0$. The sharp nine role cuts $0 = t_{0} < t_{1} < \cdots < t_{9} = T$ are the unique solution of

$$\int_{t_{j - 1}}^{t_{j}}W_{b}(t)\, dt = \frac{1}{9}\int_{0}^{T}W_{b}(t)\, dt\quad(j = 1,\ldots,9).$$

All cut gaps are uniformly bounded away from zero on the chosen compact $b$ interval: $0 < w_{*} \leq W_{b} \leq w^{*}$ implies $t_{j} - t_{j - 1} \geq w_{*}T/\left( 9w^{*} \right)$.

At formal terminal target fraction $q^{\nu}$ and compensator fraction $1 - 9q^{\nu}$, the sharp compensator ledger is

$$F_{q}(b) = \frac{R_{b}(T)^{\nu}\left( 1 - 9q^{\nu} \right) - 1}{\nu} + \int_{0}^{T}\psi_{\nu}\left( bR_{b}(t) \right)\, dt.$$ (D.7)

At $b = 0$ and $q = 0$, the integral vanishes by $\nu > 1$; moreover $H_{0} > 1$ because for the nonzero positive stage components $a,c$ we have $H_{0} = \sum v_{i}^{\nu - 1} > \sum v_{i}^{\nu} = 1$. Therefore $F_{0}(0) = \left( R_{0}(T)^{\nu} - 1 \right)/\nu > 0$ for every finite $T$. At $b = b_{+}$, $\psi_{\nu}\left( b_{+}R_{b_{+}}(t) \right) < 0$ for all $t$, and its value converges to the strictly negative constant $\psi_{\nu}\left( b_{+}H_{b_{+}} \right)$ as $t \rightarrow \infty$. Consequently the integral in (D.7) tends to $- \infty$ linearly with $T$, while the terminal term remains bounded. Choose one finite $T$ for which $F_{0}\left( b_{+} \right) < 0$. By continuity as $b \downarrow 0$, choose $0 < b_{-} < b_{+}$ with $F_{0}\left( b_{-} \right) > 0$. Finally choose $0 < q_{0} < c/2$ small enough that both strict signs persist uniformly for all $q \in \left\lbrack 0,q_{0} \right\rbrack$.

## D.2. Uniform positive smoothing and exact account closure

Inside the nine stages, the directions are permutations of one fixed positive vector. Smooth every internal cut by an $h$-wide affine interpolation in the *fractions* $Y_{i}$, and similarly interpolate the initial equal fractions and the terminal $\left( q^{\nu},\ldots,q^{\nu},1 - 9q^{\nu} \right)$. The sharp interior cuts have a compact positive separation, so all ramps are disjoint for one sufficiently small fixed $h > 0$. The smoothed radial source $H_{\nu}(Y)$ differs from the sharp source only on the $11$ ramp intervals, of total length $O(h)$. Since $1 \leq H_{\nu}(Y) \leq 10^{1/\nu}$, variation of constants gives $\parallel R_{h} - R_{b} \parallel_{\infty} = O(h)$, uniformly in $b \in \left\lbrack b_{-},b_{+} \right\rbrack$ and $q \in \left\lbrack 0,q_{0} \right\rbrack$. The ledger integrands $\psi_{\nu}\left( RY_{i}^{1/\nu} \right)$ are uniformly bounded even as $q \downarrow 0$, and their radial derivatives remain bounded because

$$\partial_{R}\psi_{\nu}\left( RY_{i}^{1/\nu} \right) = \nu R^{\nu - 1}Y_{i} - (\nu - 1)R^{\nu - 2}Y_{i}^{(\nu - 1)/\nu}.$$

Hence ledger residuals differ from their sharp counterparts by $O(h)$, uniformly over those parameters.

Let $D_{j}^{h} = X_{j}^{h}(T) - X_{j + 1}^{h}(T)$ for targets $j = 1,\ldots,8$, and let $t$ denote the eight free internal cut times. At the sharp equal-weight root,

$$\partial_{t}D^{0} = L_{8}diag\left( W_{b}\left( t_{1} \right),\ldots,W_{b}\left( t_{8} \right) \right),\quad\quad \parallel \left( \partial_{t}D^{0} \right)^{- 1} \parallel_{\infty} \leq 10/w_{*}.$$ (D.8)

The determinant is $9\prod_{j = 1}^{8}W_{b}\left( t_{j} \right) > 0$. The moving-ramp derivative of $R_{h}$ satisfies the same localized-pulse identity as (C.5); its $L^{1}$ norm and terminal value are $O(h)$ uniformly in $b,q$, because the two stages flanking any internal cut are permutations and have identical radial sources. The direct derivative from translating the $Y$ interpolation converges to the exact neighboring sharp-stage jump by the fundamental theorem of calculus on the fixed positive internal fraction interval. Its convergence is uniform because all *internal* stage components are at least $\min\left( c,b_{-} \right)^{\nu} > 0$. The terminal ramp may contain $q = 0$ but is fixed while the internal cuts vary; no derivative with respect to $q$ is used. These observations establish

$$\sup_{b,q,t} \parallel \partial_{t}D^{h} - \partial_{t}D^{0} \parallel_{\infty} \rightarrow 0\quad\quad(h \downarrow 0)$$

on a fixed small compact neighborhood of the ordered sharp cut roots. The analogous uniform residual convergence holds for $D^{h} - D^{0}$.

Using the explicit inverse bound (D.8), choose a common cut ball radius $r > 0$ such that the sharp preconditioned Jacobian differs from the identity by less than $1/4$ throughout the ball. Then choose a single $h > 0$, independent of $q \in \left\lbrack 0,q_{0} \right\rbrack$, making the additional preconditioned derivative error $< 1/4$ and the center residual displacement $< r/2$. The map

$$t \mapsto t - \left( \partial_{t}D^{0} \right)^{- 1}D^{h}(b,q,t)$$

therefore contracts each ball with constant at most $1/2$, remains inside that ball, and has a unique ordered exact cut-time root continuous in $b,q$. At the root the smoothed compensator ledger remains uniformly close to (D.7), so the strict opposite endpoint signs at $b_{-},b_{+}$ persist. The intermediate value theorem selects some $b = b(q)$ closing it exactly. All nine target ledgers are equal, and the exact paired-dollar identity $\sum_{i}^{}X_{i}(T) = 0$ forces each target ledger to vanish.

## D.3. A single finite-dollar and inventory envelope

Along each smoothed path, $1 \leq R \leq 10^{1/\nu}$ and $Y_{i}$ remains in the simplex. On a fixed-width affine ramp $\left| {\dot{Y}}_{i} \right| \leq 1/h$, and outside ramps it vanishes. The formula (D.2) therefore yields a finite parameter-uniform bound on $\max_{i,t}\left| {\dot{u}}_{i} \right|$ for all $q \in (0,q_{0}\rbrack$. Choose $a_{0}$ larger than that bound, set $K = 1/a_{0}$, and realize every net rate by Lemma 8.1, prescribing *actual* equal gross dollar activity $a_{0}$ at each node. The total paired turnover is the fixed finite $M = 10a_{0}T/2$. Before the terminal ramp every target has $Y_{i} \geq c^{\nu}$, so $x_{i} \geq c$. In that ramp the positive-price and gross sale-share estimates are precisely (D.4); thus for all targets

$$H_{i}^{-} \leq a_{0}\left( \frac{T}{c} + \frac{h\nu}{c(\nu - 1)} \right).$$

The compensator fractions are at least $b_{-}^{\nu}$ before and during the final ramp (the final fraction is positive and larger than $b_{-}^{\nu}$ after reducing $q_{0}$ if needed), so $x_{10} \geq b_{-}$ and $H_{10}^{-} \leq a_{0}T/b_{-}$. A single finite $H_{0}$ dominates these fixed bounds.

The nine terminal target prices are $qR(T)$ and the tenth price is at most $10^{1/\nu}$. Thus

$$\begin{matrix}
Q_{0.9}(T) & \geq \log(1/q) - \left( \log 10 \right)/\nu, \\
\overline{L}(T) & \geq \frac{9}{10}\log(1/q) - \left( \log 10 \right)/\nu.
\end{matrix}$$

Both diverge as $q \downarrow 0$, while $M$, $H_{0}$, $T$, $K$ and $h$ remain fixed. Positivity holds for every strictly positive $q$; the formal $q = 0$ limit is never counted as an admissible path. The constants may deteriorate rapidly as $p \uparrow 1$, so the proof makes no claim uniform in the response exponent.

# E. Independent interval checker for Construction III

The executable is `verification/activity_driven/certify_five_targets.py`. It does not use V16's physical-time ODE or its 80,000-step certificate. Its price primitive is integrated from (8.6); explicit antiderivatives are

$$\begin{matrix}
P_{+}(s) & = - \frac{1}{4}\log\left( \frac{3}{2} - 2\left( s - \frac{1}{2} \right)^{2} \right) + \frac{1}{2\sqrt{3}}artanh\left( \frac{2\left( s - \frac{1}{2} \right)}{\sqrt{3}} \right), \\
P_{-}(s) & = \frac{1}{4}\log\left( 2\left( s - \frac{1}{2} \right)^{2} + \frac{1}{2} \right) + \frac{1}{2}\arctan(2s - 1).
\end{matrix}$$

The program computes these with outward-rounded interval operations; the arctangent uses a finite alternating Taylor series with a separately included geometric remainder after the argument reduction $\arctan(t) = \pi/4 + \arctan\left( (t - 1)/(t + 1) \right)$. Each inverse is enclosed by rational endpoints whose primitive interval evaluations lie strictly below and above the desired primitive interval. The root is isolated by strict interval signs at (8.8); all path prices for the resulting exact root are then propagated as intervals. Since buying and selling have strictly monotone price flows on the certified ranges, checking all event endpoints proves the sessionwise bounds between events. A second internally independent implementation, now archived at `research/v19-activity-recovery/verify_c1_independent_rational.py`, uses a $10^{- 65}$ exact rational grid with directed rounding, explicit Taylor remainder enclosures, and an independently bracketed inverse-primitive algorithm. Its agreement with the original checker strengthens internal cross-validation but is not third-party formal verification. Both programs must pass. The checker then verifies interval upper bounds on $M$, the per-asset dollar sales and conservative share inventories, the specified physical-time rate schedule, and the elementary exact inequality $(9/16)1.23 < {0.84}^{2}$. It prints a JSON evidence record. The JSON records the certified rate schedule separately from a historical floating-point trial rate of $0.28$; these are not interchangeable. The checker's scope is an *internally implemented* interval proof, not a formally verified implementation or external independent peer review.

# References

\[1\] A. Alfonsi and A. Schied, "Optimal trade execution and absence of price manipulations in limit order book models," *SIAM J. Financial Math.*, vol. 1, pp. 490--522, 2010, doi: [10.1137/090762786](https://doi.org/10.1137/090762786).

\[2\] R. Almgren and N. Chriss, "Optimal execution of portfolio transactions," *J. Risk*, vol. 3, no. 2, pp. 5--39, 2001, doi: [10.21314/JOR.2001.041](https://doi.org/10.21314/JOR.2001.041).

\[3\] P. Bank and D. Baum, "Hedging and portfolio optimization in financial markets with a large trader," *Math. Finance*, vol. 14, no. 1, pp. 1--18, 2004, doi: [10.1111/j.0960-1627.2004.00179.x](https://doi.org/10.1111/j.0960-1627.2004.00179.x).

\[4\] A. Bressan and F. Rampazzo, "On differential systems with vector-valued impulsive controls," *Boll. Un. Mat. Ital. B (7)*, vol. 2, no. 3, pp. 641--656, 1988, Available: <https://www.math.sissa.it/publication/differential-systems-vector-valued-impulsive-controls>

\[5\] M. K. Brunnermeier and L. H. Pedersen, "Predatory trading," *J. Finance*, vol. 60, no. 4, pp. 1825--1863, 2005, doi: [10.1111/j.1540-6261.2005.00781.x](https://doi.org/10.1111/j.1540-6261.2005.00781.x).

\[6\] G. Cespa and T. Foucault, "Illiquidity contagion and liquidity crashes," *Rev. Financ. Stud.*, vol. 27, pp. 1615--1660, 2014, doi: [10.1093/rfs/hhu016](https://doi.org/10.1093/rfs/hhu016).

\[7\] U. Çetin, R. A. Jarrow, and P. Protter, "Liquidity risk and arbitrage pricing theory," *Finance Stoch.*, vol. 8, no. 3, pp. 311--341, 2004, doi: [10.1007/s00780-004-0123-x](https://doi.org/10.1007/s00780-004-0123-x).

\[8\] R. Cont and L. Wagalath, "Running for the exit: Distressed selling and endogenous correlation in financial markets," *Math. Finance*, vol. 23, pp. 718--741, 2013, doi: [10.1111/j.1467-9965.2011.00510.x](https://doi.org/10.1111/j.1467-9965.2011.00510.x).

\[9\] J. Gatheral, "No-dynamic-arbitrage and market impact," *Quant. Finance*, vol. 10, pp. 749--759, 2010, doi: [10.1080/14697680903373692](https://doi.org/10.1080/14697680903373692).

\[10\] G. Gennotte and H. Leland, "Market liquidity, hedging, and crashes," *Amer. Econ. Rev.*, vol. 80, pp. 999--1021, 1990, Available: <https://ideas.repec.org/a/aea/aecrev/v80y1990i5p999-1021.html>

\[11\] J. Huang and J. Wang, "Liquidity and market crashes," *Rev. Financ. Stud.*, vol. 22, pp. 2607--2643, 2009, doi: [10.1093/rfs/hhn086](https://doi.org/10.1093/rfs/hhn086).

\[12\] G. Huberman and W. Stanzl, "Price manipulation and quasi-arbitrage," *Econometrica*, vol. 72, pp. 1247--1275, 2004, doi: [10.1111/j.1468-0262.2004.00531.x](https://doi.org/10.1111/j.1468-0262.2004.00531.x).

\[13\] Japan Exchange Group, "Daily price limits: Trading rules of domestic stocks." <https://www.jpx.co.jp/english/equities/trading/domestic/06.html>. Accessed October 2026.

\[14\] A. A. Obizhaeva and J. Wang, "Optimal trading strategy and supply/demand dynamics," *J. Financial Markets*, vol. 16, pp. 1--32, 2013, doi: [10.1016/j.finmar.2012.09.001](https://doi.org/10.1016/j.finmar.2012.09.001).

\[15\] D. Romer, "Rational asset-price movements without news," *Amer. Econ. Rev.*, vol. 83, pp. 1112--1130, 1993, Available: <https://www.nber.org/papers/w4121>

\[16\] Y. Yang, "Finite horizon optimal execution with bounded rate of transaction," *Stoch. Models*, vol. 35, pp. 469--495, 2019, doi: [10.1080/15326349.2019.1621760](https://doi.org/10.1080/15326349.2019.1621760).

*Author affiliation:* Independent Researcher.