# 论文结果与 Lean 基础映射

状态日期：2026-10-17。权威文本paper/main.tex。原始编号严格验收 **10/16**；接受结果和精确同SHA CI见单一入口 WHOLE_PAPER_LEAN_COMPLETION.md 及下列逐项行。Theorem1.1是非正式概览，不单计第17项。除明确授权的A01边界外不改数学主张。

固定 Lean/Mathlib 下最新已审计的数学源码含 **197/197 个 kernel-checked 定理声明**；其中 `proposition_7_1_original_endpoint` 和 `proposition_7_1_single_compensator` 覆盖原文 Proposition 7.1 的完整条件性终端结论。[核审计 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38983955426)。其余编号结果须按原文全量词单独验收，不能以辅助声明数量替代。

关于 3.1/3.2 的新增 Lean 结果必须注意：已由**全正价格域**的弹性下界导出两类坐标凹性，并在纯恢复离散步骤中证明了势函数非负保持；但**所有可容许路径**（连续交易与恢复同时发生、脉冲交易、终点账本）仍未形式化，因此不能将条件性端点引理升格为原定理的完整证明。全文验收标准见 [Issue #5](https://github.com/Siyuan-chat/market-crash-reachability/issues/5)；新增源文件见 `formal/lean/MarketCrash/CrisisFunctional.lean` 和 `formal/lean/MarketCrash/BarrierEndpoint.lean`。

[M1–M5 model-fidelity audit](MODEL_FIDELITY.md) 记录正则路径证明 `admissible_regular_no_all_asset_decline`、`admissible_regular_no_systemic_crisis` 与原论文更大有限变差路径类的尚未解决的关系。故两项原文定理的整项 Lean 状态暂不升级。

## Theorem 1.1 — thm:informal

证据：paper/main.tex:62。整项 Lean 状态：未形式化。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[Main results, informal]\label{thm:informal}
Under the paired-dollar, resilient market defined in Section~\ref{sec:model}, the following conclusions hold.
\begin{enumerate}[label=\textup{(\roman*)},leftmargin=2em,itemsep=0.12em]
\item \emph{Structural exclusion.} If $e(S)=Sg'(S)/g(S)\ge2$ at all admissible prices, then $\Cris_\alpha(t)\le0$ for every breadth and time. The weaker condition $e(S)\ge1$ excludes a simultaneous decline of all assets.
\item \emph{Reachability regimes.} With $g_p(S)=\eta(S/F)^p$, $p=2,1,0$ respectively produce exclusion, inventory-bounded partial-coverage drawdowns, and, for $k=\lceil\alpha N\rceil<N$ and sufficiently long finite horizons, arbitrarily severe partial-coverage losses under fixed finite turnover and inventory caps when pulses are allowed. For constant impact and $k=N$, a sharp horizon-dependent bound replaces unrestricted severity.
\item \emph{Execution resources.} General positive $g$ yields explicit necessary dollar-turnover and share-inventory bounds. With constant per-share impact and bounded gross executed-share rates, the small-rate crisis bound is quadratic and this order is attained by a continuous dollar-closed construction.
\item \emph{Multiday execution.} Rolling price bands restrict per-session losses, while rate limits and the receiving assets' capacity restrict consecutive lower-limit closes. A computer-assisted two-day ten-asset path satisfies these controls, has nine repeated lower-limit closes, and yields $\Cris_{0.9}(T)>0.020$; for that instance, $0.044<\bar v_*<0.285$.
\end{enumerate}
\end{theorem}
```

## Theorem 3.1 — thm:barrier1

证据：paper/main.tex:193。整项 Lean 状态：**PAPER_ACCEPTED**；B02 Theorem 3.1 PAPER_ACCEPTED；证明 SHA `dbb5c784b07b6f8fc5ec3738410346fffc7cc47c`；本地完整构建、360项公理审计及245项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617907)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617901)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617894)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617891)。 canonical `theorem_3_1_original`；见 B02_SCOPE_AUDIT.md。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[Barrier to a decline of every asset]\label{thm:barrier1}
If $e(S)\ge1$ at all prices attainable by admissible paths, then $S_i(t)<F$ for every $i$ is impossible at any time $t$. In particular, no positive crisis with $k=N$ is reachable.
\end{theorem}
```

## Theorem 3.2 — thm:barrier2

证据：paper/main.tex:200。整项 Lean 状态：**PAPER_ACCEPTED**。B03 Theorem 3.2 PAPER_ACCEPTED；证明 SHA `e80b03c0431ab0a8de444931f96ffa037e2b68f2`；本地全量构建、362项公理审计及247项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188459)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188372)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188404)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188355)。 canonical `theorem_3_2_original`，详见 B03_SCOPE_AUDIT.md。

```latex
\begin{theorem}[Barrier to a systemic crisis of any breadth]\label{thm:barrier2}
If $e(S)\ge2$ on the admissible price range, then for every admissible control, $N\ge2$, $\alpha\in(0,1]$ and $t\in[0,T]$,
\begin{equation}\label{eq:no-crash}
\boxed{\Cris_\alpha(t)\le0.}
\end{equation}
Thus no strictly positive systemic terminal-crisis threshold can be reached.
\end{theorem}
```

## Theorem 4.1 — thm:ABC

证据：paper/main.tex:241。整项 Lean 状态：未形式化。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[A/B/C reachability regimes]\label{thm:ABC}
Let $N\ge2$ and $k=\lceil\alpha N\rceil<N$. Compare the three markets in \eqref{eq:power} under the same model protocol.
\begin{enumerate}[label=\textup{(\Alph*)},leftmargin=2em,itemsep=0.15em]
\item \textbf{Barrier market ($p=2$):} $\Cris_\alpha(t)\le0$ for every admissible path and every horizon.
\item \textbf{Inventory-bounded market ($p=1$):} positive but sufficiently small terminal systemic drawdowns are reachable. If every asset starts with a fixed finite inventory cap $H_0$ and short selling is forbidden, the terminal crisis severity is bounded above independently of the trade sequence.
\item \textbf{Severely reachable market ($p=0$):} for every fixed $N\ge2$ and $k<N$, there exists a sufficiently long but finite horizon $T$ and finite constants $M_0,H_0$ such that, for \emph{every} finite $\delta>0$, an admissible positive-price path with $M\le M_0$, $H_i^-\le H_0$, and $X_i(T)=0$ attains $\Cris_\alpha(T)>\delta$.
\end{enumerate}
The constants in (C) may depend on $N,T,F,\rho,\eta$, but not on $\delta$. They do not remain uniform as $N\to\infty$.
\end{theorem}
```

## Proposition 4.2 — prop:three-pulse

证据：paper/main.tex:262。整项 Lean 状态：**PAPER_ACCEPTED**，完整三脉冲与公共余项已验收，精确SHA/CI如下。

```latex
\begin{proposition}[Local all-asset decline]\label{prop:three-pulse}
If $g$ is $C^3$ near $F$ and $e(F)<1$, then for every $N\ge2$ there exists a terminally dollar-closed, positive-price, small-amplitude three-pulse control under which \emph{every} $S_i(T)<F$. With $c=g(F)/F^2$ and $r=e^{-\rho T/2}$, the losses of a zero-sum impulse direction $\bm u$ with every $u_i\ne0$ satisfy
\begin{equation}\label{eq:three-pulse}
L_i(T)=\frac{1-e(F)}2c^2h^2u_i^2r(1-r^2)+O(h^3)>0
\end{equation}
for sufficiently small $h>0$.
\end{proposition}
```

C01 Proposition 4.2 PAPER_ACCEPTED；证明 SHA `c58a3287c94d3bcc56386a7715657fad489ec8be`；本地全量构建、500项公理审计和264项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791535)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791496)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791519)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791505)。 canonical `proposition_4_2_original_uniform`，见 C01_SCOPE_AUDIT.md。

## Proposition 4.3 — prop:two-pulse

证据：paper/main.tex:273。整项 Lean 状态：**LEAN_PASS**，完整双脉冲、502项公理审计和266项哈希PASS，同SHA CI待验收，见 C02_SCOPE_AUDIT.md。

```latex
\begin{proposition}[Local partial-coverage decline]\label{prop:two-pulse}
Let $k<N$, $e_0=e(F)<2$, and $r=e^{-\rho T}<2-e_0$. Select a zero-sum dollar direction with at least $k$ positive components and execute $h\bm u$ at time $0$ and $-h\bm u$ at time $T$. Then $\Cris_\alpha(T)>0$ for all sufficiently small $h>0$, and
\begin{equation}\label{eq:two-pulse}
\overline L(T)=\frac{c^2h^2}{2N}(1-r)(2-e_0-r)\sum_iu_i^2+O(h^3).
\end{equation}
\end{proposition}
```

## Theorem 4.4 — thm:critical

证据：paper/main.tex:297。整项 Lean 状态：未形式化。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[Sharp all-asset horizon threshold]\label{thm:critical}
Under Assumption~\ref{asmp:model} with $g(S)=\eta$ and $k=N$, define
\begin{equation}\label{eq:critical}
\boxed{\delta_{\mathrm{crit}}(N,T)=
\log\frac{\sqrt N}{1+(\sqrt N-1)e^{-\rho T}}.}
\end{equation}
For every $\delta\in(0,\delta_{\mathrm{crit}}(N,T))$, some admissible terminally dollar-closed control reaches $\Cris_1(T)\ge\delta$ with finite turnover and sufficiently large finite inventory. If $\delta\ge\delta_{\mathrm{crit}}(N,T)$, no such positive-price path exists. Thus $\delta_{\mathrm{crit}}$ is the \emph{unattained supremum} of the all-asset common log drawdown.
\end{theorem}
```

## Theorem 5.1 — thm:resource

证据：paper/main.tex:317。整项 Lean 状态：**PAPER_ACCEPTED**。B04 Theorem 5.1 PAPER_ACCEPTED；证明 SHA `a1415e9745b65581a3c3053cc45be56c3763181c`；本地全量构建、413项公理审计及251项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767964)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767913)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768014)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768057)。 canonical `theorem_5_1_original`；见 B04_SCOPE_AUDIT.md。

```latex
\begin{theorem}[Execution-resource lower bounds]\label{thm:resource}
Suppose an admissible terminal path satisfies $\Cris_\alpha(T)\ge\delta>0$. Write $k=\lceil\alpha N\rceil$ and $s=Fe^{-\delta}$. Besides $\Phi$, define the monotone share-response coordinate $\Psi(S)=\int_F^S\dd u/g(u)$. Then the necessary dollar-turnover and total share-sale bounds are simply the respective coordinate distances to $s$:
\begin{equation}\label{eq:resource-lower}
\boxed{M\ge -k\Phi(s)=k\int_s^F\frac{u}{g(u)}\dd u,\qquad
\sum_iH_i^-\ge -k\Psi(s)=k\int_s^F\frac{\dd u}{g(u)}.}
\end{equation}
Moreover, if $X_i(T)=0$, no short sales are allowed, and the initial inventory of any qualifying asset does not exceed $H_i$, then
\begin{equation}\label{eq:share-bound}
\boxed{\int_s^F\frac{F-u}{g(u)}\dd u\le FH_i.}
\end{equation}
These inequalities are necessary, not sufficient, and need not be sharp.
\end{theorem}
```

## Proposition 6.1 — prop:rate-band

证据：paper/main.tex:365。整项 Lean 状态：**PAPER_ACCEPTED，`de95f967b533794677012281432b401aab4517b3` 四项同 SHA CI 全绿**。完整定理族：`proposition_6_1_rate_only`、`proposition_6_1_rate_band`、`proposition_6_1_hypothetical_reset`；全量本地构建和245项公理审计通过，量词/假设映射见 [A02_SCOPE_AUDIT.md](A02_SCOPE_AUDIT.md)。

```latex
\begin{proposition}[Rate and price-band exclusion certificates]\label{prop:rate-band}
Suppose the common impact function is positive and $g(S)\le G$ on the whole admissible price region. Under the cap~\eqref{eq:grossrate}, every asset obeys
\begin{equation}\label{eq:rate-floor}
 S_i(t)\ge F-\frac{G\bar v}{\rho}(1-e^{-\rho t}),\qquad 0\le t\le T.
\end{equation}
Under the additional price band~\eqref{eq:band}, put
\begin{equation}\label{eq:twofloors}
 S_{\rm floor}=\max\!\left\{F(1-\beta_-),\;F-\frac{G\bar v}{\rho}(1-e^{-\rho T})\right\}>0.
\end{equation}
Then for any breadth $\alpha$ and any admissible control,
\begin{equation}\label{eq:constrained-crisis}
\boxed{\ \mathcal C_\alpha(t)\le \log\frac{F}{S_{\rm floor}}\quad\hbox{for all }t\le T.\ }
\end{equation}
In particular, a necessary finite-speed condition to reach threshold $\delta>0$ is
\begin{equation}\label{eq:min-speed}
\boxed{\ \bar v\ge\frac{\rho F(1-e^{-\delta})}{G(1-e^{-\rho T})}.\ }
\end{equation}
A one-session lower price limit independently excludes any $\delta> -\log(1-\beta_-)$. These are \emph{necessary} constraints, generally not sharp reachability thresholds. For comparison, if a \emph{hypothetical} multi-session regime resets a proportional lower band to each preceding close, then over $D$ sessions the elementary bound is only
$S_i(T_D)\ge F\prod_{d=1}^D(1-\beta_{-,d})$ and
$\mathcal C_\alpha(T_D)\le-\sum_{d=1}^D\log(1-\beta_{-,d})$.
Thus a daily band cannot be interpreted as a permanent, fixed-baseline ban on a cumulative crash. Actual TSE limits are price-tiered yen rules, not these proportional resets.
\end{proposition}
```

## Theorem 6.2 — thm:quadratic-rate

证据：paper/main.tex:411。整项 Lean 状态：未形式化。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[A quadratic small-rate crisis barrier for constant impact]\label{thm:quadratic-rate}
Let $g(S)\equiv\eta>0$, assume dollar pairing $\sum_iS_i\dot\theta_i=0$, and impose the gross share-rate cap~\eqref{eq:grossrate}. Write $d_T=1-e^{-\rho T}$ and
\begin{equation}\label{eq:bsmall}
 b_T=\frac{\eta\bar v}{F\rho}\,d_T<1.
\end{equation}
Then, with or without terminal dollar closure and for \emph{every} $N\ge2$ and breadth $\alpha$,
\begin{equation}\label{eq:quadratic-rate}
\boxed{\ \mathcal C_\alpha(T)\le
\left(\frac{\eta\bar v}{F\rho}\right)^2
\left[d_T-\rho T e^{-\rho T}
 +\frac{d_T^2}{2(1-b_T)^2}\right].\ }
\end{equation}
In particular, the maximum possible positive crisis severity is $O(\bar v^2)$ as $\bar v\downarrow0$. For fixed $N,T$ and any positive price-band width, this \emph{order is attained} by the continuous control of Theorem~\ref{thm:finite-rate-construct}, and hence its minimum required gross execution-rate cap obeys $\bar v_*(\delta)=\Theta(\sqrt\delta)$ as $\delta\downarrow0$ in the constant-impact market. The implied coefficients depend on the prescribed control and are not an exact optimization solution.
\end{theorem}
```

## Theorem 6.3 — thm:finite-rate-construct

证据：paper/main.tex:441。整项 Lean 状态：未形式化。数学证明状态：原文纸面证明（1.1 仅为概览）；已有符号/数值检查不替代整项形式化。

```latex
\begin{theorem}[Positive all-asset decline with bounded continuous execution]\label{thm:finite-rate-construct}
Assume $g\in C^3$ near $F$, $g(F)>0$, $\rho>0$, and $e_0=Fg'(F)/g(F)<1$. Fix \emph{any} $N\ge2$, horizon $T>0$, rate cap $\bar v>0$, one-session band widths $\beta_-,\beta_+>0$, and any fixed positive amount of initially available shares per asset. Then there exists an \emph{absolutely continuous}, paired-dollar, per-asset gross-rate-bounded control, remaining strictly inside the band, with $X_i(T)=0$ for each asset and
\begin{equation}\label{eq:local-speed-crash}
 \boxed{\ S_i(T)<F\ \text{for every }i,\qquad \mathcal C_1(T)>0.\ }
\end{equation}
The attained loss can be arbitrarily small. This does \emph{not} assert that a prescribed fixed large threshold remains reachable under an arbitrarily tight cap or band.
\end{theorem}
```

## Proposition 7.1 — prop:multiday-crisis-trigger

证据：paper/main.tex:526。**整项 Lean 状态：PAPER_ACCEPTED（首项验收结果）**。Lean 定理：`proposition_7_1_original_endpoint`、`proposition_7_1_single_compensator`，连同 `proposition_7_1_exact_severity` 及两种分位数情形；197/197 核心定理和公理审计通过。证明严格是原文的**条件性终端等价式**，不声称任意给定收盘配置可以动态实现。

```latex
\begin{proposition}[A conditional systemic-crisis trigger test]\label{prop:multiday-crisis-trigger}
Suppose the same $k=\lceil\alpha N\rceil<N$ assets close at $Fq^D$ after $D$ identical proportional-reset sessions, with $q\in(0,1)$. Let the remaining $N-k$ assets close at $Y_j>0$, and write $\lambda=-\log q$. For any $0<\delta\le D\lambda$, the \emph{terminal} crisis threshold $\Cris_\alpha(T_D)\ge\delta$ holds if and only if
\begin{equation}\label{eq:multiday-trigger-product}
\boxed{\qquad \prod_{j=1}^{N-k}\frac{Y_j}{F}
 \le\exp\bigl(kD\lambda-N\delta\bigr).\qquad}
\end{equation}
If all other assets have individual log losses at most $D\lambda$ (or if $k>N/2$, so the $N-k$ other assets cannot fill the top $k$ ranks), then $Q_\alpha(T_D)=D\lambda$ and the terminal crisis severity is exactly
\begin{equation}\label{eq:multiday-trigger-exact}
\boxed{\quad\Cris_\alpha(T_D)=\min\!\left\{D\lambda,
 \frac{kD\lambda-\sum_{j=1}^{N-k}\log(Y_j/F)}{N}\right\}.\quad}
\end{equation}
In particular, with a single compensator ($k=N-1$), its terminal price must obey $Y/F\le\exp(kD\lambda-N\delta)$ if a crisis of threshold $\delta$ is to occur. These are exact \emph{conditional endpoint identities}, not sufficient conditions for a trade path realizing the stipulated closing prices.
\end{proposition}
```

## Proposition 7.2 — prop:rolling-rate

证据：paper/main.tex:551。整项 Lean 状态：**PAPER_ACCEPTED，证明 SHA `5c84995094b736c0231df6d804c8daad638bbfc7`，四项同 SHA CI SUCCESS**。`proposition_7_2_single_session`、`proposition_7_2_rolling_streak`、`proposition_7_2_perpetual_and_integer` 完整覆盖三分支；见 [A03_SCOPE_AUDIT.md](A03_SCOPE_AUDIT.md)。

```latex
\begin{proposition}[Rolling-limit shock-rate certificates]\label{prop:rolling-rate}
In the constant per-share impact model, a lower-limit close in a session starting at $s>0$ requires
\begin{equation}\label{eq:single-session-streak-rate}
 \boxed{\quad\bar v\ge \left[\frac{\rho}{\eta}\left(F-s+
 \frac{\beta s}{1-e^{-\rho\tau}}\right)\right]_+.\quad}
\end{equation}
If the same asset closes at the same proportional lower limit on each of $D$ sessions of common duration $\tau$, with $s_d=Fq^{d-1}$, then
\begin{equation}\label{eq:D-streak-speed}
\boxed{\quad\bar v\ge\frac{\rho F}{\eta}\max_{1\le d\le D}
 \left[1+q^{d-1}\left(\frac{1-q}{1-e^{-\rho\tau}}-1\right)\right].\quad}
\end{equation}
Moreover, when $\eta\bar v<\rho F$, all prices starting at $F$ obey the perpetual \emph{rate-only} floor $S_i(t)\ge F-\eta\bar v/\rho$, implying the necessary integer-streak bound
\begin{equation}\label{eq:streak-D-bound}
\boxed{\quad D\le\frac{\log(1-\eta\bar v/(\rho F))}{\log q}.\quad}
\end{equation}
The bound is understood only for $\eta\bar v<\rho F$; with a larger rate cap it supplies no finite-day obstruction. None of these scalar inequalities is sufficient for multi-asset price-band feasibility or terminal dollar closure.
\end{proposition}
```

## Theorem 7.3 — thm:no-second-global

证据：paper/main.tex:577。整项 Lean 状态：**PAPER_ACCEPTED**。B06 Theorem 7.3 PAPER_ACCEPTED；证明 SHA `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；本地全量构建、436项公理审计和255项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980258)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980348)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980253)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980257)。 canonical `theorem_7_3_original`，见 B06_SCOPE_AUDIT.md。

```latex
\begin{theorem}[An obstruction to a second all-asset limit-down close]\label{thm:no-second-global}
Assume $g_i(S)>0$, $\rho_i>0$, unchanged fundamental benchmarks $F_i>0$, and instantaneous interasset executed-dollar balance $\sum_i\dd X_i=0$. Suppose every asset closes the first session at $S_i(T_1)=q_iF_i<F_i$, and the \emph{entire second-session admissible band} lies at or below its own benchmark,
\begin{equation}\label{eq:no-second-condition}
 (1+\beta_{i,2,+})q_i\le1\quad\text{for every }i.
\end{equation}
Then it is impossible for \emph{every} asset to close the second session strictly below its first close. In particular, simultaneous second-day lower-limit closes in all $N$ assets are impossible. This holds regardless of the transaction-rate cap, terminal signed-dollar balances, or the functional form of the positive $g_i$.
\end{theorem}
```

## Proposition 7.4 — prop:streak-precondition

证据：paper/main.tex:600。整项 Lean 状态：**PAPER_ACCEPTED**。B05 Proposition 7.4 PAPER_ACCEPTED；证明 SHA `131256911c0d21ff837a477cc63c8241ebcb27c7`；本地全量构建、433项公理审计和253项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405730)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405801)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405755)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405739)。 canonical `proposition_7_4_original`，见 B05_SCOPE_AUDIT.md。

```latex
\begin{proposition}[Preconditioning needed for a dollar-closed limit-down streak]\label{prop:streak-precondition}
Let an asset begin at $F$ and finish $D$ sessions at $s_D<F$, with $X_i(T_D)=0$. Then its trajectory necessarily visits $S_i>F$ on a set of positive trading-time measure and satisfies
\begin{equation}\label{eq:streak-excursion}
 \rho\int_0^{T_D}\frac{S_i(t)(S_i(t)-F)}{g(S_i(t))}\dd t
 =\int_{s_D}^{F}\frac{u}{g(u)}\dd u>0.
\end{equation}
If every session after the first keeps the asset at or below $F$, and the first-session upper band is $U_1>F$, a necessary condition is
\begin{equation}\label{eq:streak-precondition}
 \boxed{\quad \rho\tau_1\max_{F\le u\le U_1}\frac{u(u-F)}{g(u)}
 \ge \int_{s_D}^{F}\frac{u}{g(u)}\dd u.\quad}
\end{equation}
For constant impact $g=\eta$, and $s_D=Fq^D$, $U_1=F(1+\beta_+)$, this simplifies to
$\rho\tau_1\ge(1-q^{2D})/[2\beta_+(1+\beta_+)]$.
Writing $H_+=\rho\tau_1\beta_+(1+\beta_+)$, whenever $2H_+<1$ this imposes the additional necessary streak-length bound
\begin{equation}\label{eq:multiday-preconditioning-D}
\boxed{\quad D\le \frac{\log(1-2H_+)}{2\log q}.\quad}
\end{equation}
This bound is specific to terminal dollar closure and the absence of above-fundamental excursions in later sessions. It is not sufficient to produce a consecutive limit-down path.
\end{proposition}
```

## Proposition 7.5 — prop:market-cut

证据：paper/main.tex:626。整项 Lean 状态：**PAPER_ACCEPTED，证明 SHA `772d72d6c3b819814ce39a165a1bb56ad6729ee6`，四项同 SHA CI 成功**。完整定理族为 `proposition_7_5_market_cut`、`proposition_7_5_ledger_derivative_bound`、`proposition_7_5_empty_complement`、`proposition_7_5_rolling_constant_impact`。原始价格积分方程到响应坐标积分由已证明的 Lipschitz FTC 导出，不预设端点式。用户明确批准非空 J 与零容量分支边界修正；逐项量词核对见 [A01_SCOPE_AUDIT.md](A01_SCOPE_AUDIT.md)。验收分子已从1提高到2；[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704394)；[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704369)；[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704465)；[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704392)。

```latex
\begin{proposition}[A market-cut capacity and consecutive-limit lower bound]\label{prop:market-cut}
Fix a nonempty subset $J$ of assets and write $J^c$ for its complement. Under paired-dollar execution and the per-asset gross share-rate cap $\bar v$, every admissible absolutely continuous path satisfies, for almost every $t$,
\begin{equation}\label{eq:market-cut-instant}
\boxed{\left|\sum_{i\in J}\dot X_i(t)\right|\le
\bar v\min\left\{\sum_{i\in J} S_i(t),\sum_{j\in J^c}S_j(t)\right\}.}
\end{equation}
Suppose that throughout a session $[T_{d-1},T_d]$ of length $\tau_d$, each $i\in J$ stays at or below its unchanged benchmark $F_i$ and ends at $s_{i,d}<s_{i,d-1}$. Let $\Phi_i'(S)=S/g_i(S)>0$ and put
\begin{equation}\label{eq:cut-required}
K_{J,d}:=\sum_{i\in J}\big[\Phi_i(s_{i,d-1})-\Phi_i(s_{i,d})\big]>0.
\end{equation}
If $J^c\ne\varnothing$ and all compensating assets satisfy $S_j(t)\le U_{j,d}$ during that session, then the session's paired executed-dollar turnover $M_d$ and the required gross-share-rate cap satisfy
\begin{equation}\label{eq:cut-necessary}
\boxed{M_d\ge K_{J,d},\qquad
\bar v\ge\frac{K_{J,d}}{\tau_d\sum_{j\in J^c}U_{j,d}}.}
\end{equation}
When $J^c=\varnothing$, the hypothesized simultaneous strict decrease of all assets cannot occur on a session lying entirely below benchmarks.
\end{proposition}
```

## Proposition 7.6 — prop:certified-v7

证据：paper/main.tex:660。整项 Lean 状态：未形式化。外部严格区间证书只证明固定 N=10、k=9 的指定路径；不是 Lean 证明或全局最优性证明。

```latex
\begin{proposition}[A computer-assisted two-day rate certificate]\label{prop:certified-v7}
In the ten-asset specification just stated in Section~\ref{subsec:v7-certified} ($k=9$, $F=\eta=1$, $\rho=0.4$, $\tau_1=\tau_2=20$, target bands $\pm3\%$, compensator bands $\pm25\%$), there exists a continuous, absolutely continuous, fully paired-dollar path with all per-asset terminal signed-dollar ledgers exactly zero such that the same nine assets close at $0.97$ and $0.9409$, respectively, while
\begin{equation}\label{eq:v7-certified-result}
\boxed{\Cris_{0.9}(40)>0.020,\quad \bar v_{\mathrm{used}}<0.285,\quad M<3,\quad H_i^-<2\quad(1\le i\le10).}
\end{equation}
Every executed price remains inside its rolling session band. Here $M$ counts paired executed dollars once and $H_i^-$ denotes gross shares sold, so initial holdings of two shares of every asset are sufficient without shorting.
\end{proposition}
```

## 已编译的局部基础对应

参见 FORMALIZATION_STATUS.md 的逐项 Lean 名称、论文对应和限制。These are local foundations only; no complete paper theorem is claimed formalized.
