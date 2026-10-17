# Lean 形式化当前状态

状态日期：2026-10-17。唯一当前入口 [WHOLE_PAPER_LEAN_COMPLETION.md](WHOLE_PAPER_LEAN_COMPLETION.md)。原始编号验收 **16/16**。D01 Proposition 7.6 PAPER_ACCEPTED；证明 SHA `15bec0e04613c040489b71a93595861ae5c82343`；本地完整构建、1224项公理审计PASS；四项同SHA CI SUCCESS：[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033132044)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033082716)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828360)、[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828458)。本次不另列SHA-256验收门（用户最新决定）。 历史材料不覆盖当前终态；PR #10保持Draft。

> 以下阶段记录保留历史语境，不代表当前证明边界；当前验收仅以上方状态与 WHOLE_PAPER_LEAN_COMPLETION.md 为准。

## 历史记录：从原始价格 ODE 到有限正则路径的完整证明链

[MODEL_FIDELITY.md](MODEL_FIDELITY.md) 列出 M1–M5 与代码的逐项对应，以及仍需解决的范围差异。新增 `PhysicalSmoothMarket.lean`、`PhysicalPulse.lean`、`AdmissibleMarketPath.lean` 和 `AdmissiblePathBarrier.lean`，已在 GitHub Actions #38844596170 完成 76 项声明的 kernel 构建、公理审计。**这验证了一个明确的正则路径子类，不是全文定理的原始全部量词。**

## 历史记录：全文形式化工程与阶段一边界

[GitHub #5 全文验证总任务](https://github.com/Siyuan-chat/market-crash-reachability/issues/5)明确了 16 项实质性编号结果（另有非正式综述 Theorem 1.1）的逐项验收条件。[PR #6](https://github.com/Siyuan-chat/market-crash-reachability/pull/6)目前已扩展为 76 项经过 kernel/axiom 审计的声明（含有限正则物理路径的不可达性定理），但尚不能替代原文 3.1/3.2 对全部有限变差路径的结论：

- `CrisisFunctional.lean`：固定基准的平均对数损失、覆盖率分位阈值及其最小值定义；验证由非负对数价格和推出危机函数非正。仍需补齐 `k=ceil(αN)` 的有效取值与排序分位数等价证明，并连接真实价格 `log(S/F)`。
- `BarrierEndpoint.lean`：在已知势函数非负的前提下排除所有资产低于基准；证明响应坐标在对数价格下严格单调；在额外假设 `G` 为全域凹且严格增、`G(0)=0` 时，用有限 Jensen 不等式推出平均对数损失不正。
- `ElasticityConcavity.lean`：已从对**全正价格域**的 e(S)≥1 与 e(S)≥2 假设，分别导出原价格坐标与对数价格坐标凹性，且给出**仍依赖势函数非负**的条件性危机上界。原论文仅要求“可容许路径能到达的价格范围”，对应关系仍需证明，不能视为原定理已完结。
- `RecoveryPotential.lean`：已在 Lean 中证明离散**纯恢复步骤** $S'=(1-lam)F+lam S$、$0≤lam≤1$ 保持势函数非负。证明不适用于未经建模的连续交易/恢复并发过程。
- **尚未在 Lean 中导出**：原模型完整动力学势函数比较、flow-completed 脉冲中间价格正性和不变量、逐资产终点美元账本与所有可容许路径的形式化。因此 3.1、3.2 仍为“未完成整项证明”。

原始论文与 Python 区间认证保持不变；Lean 的 kernel 构建成功不意味着 7.6 的区间证书已通过 Lean 审核。

## 历史记录：Stage-1 可复现身份与实际验证

- Lean：`leanprover/lean4:v4.19.0`，证据 `lean/lean-toolchain:1`。
- mathlib：`c44e0c8ee63ca166450922a373c7409c5d26b00b`，证据 `lean/lake-manifest.json` 的 mathlib `rev` 与 `inputRev`。
- 本地构建：**passed**，由主 agent 实际执行并确认；本次文档作者未另行重跑。
- axiom 审计：**passed**，原版 34 项基础声明，加上 12 项 Stage-1 辅助引理，合计 76 项项目 theorem（包括后续物理路径结果）；已通过 GitHub Actions #38844596170 的 kernel 编译和全量 axiom 审计；仅依赖标准基础公理 propext、Classical.choice、Quot.sound。证据为 `../build/formal/axioms.log` 和 `../build/formal/integrity.json`，可由 `python formal/check_proof_integrity.py` 重现。
- 静态审查未检出 `sorry`、`admit` 或自定义 `axiom`。使用 Mathlib 和经典选择不意味着无基础公理依赖。
- 英文论文、数学内容及外部认证算法保持基线不变。

## 历史记录：Stage-1 局部基础与论文对应

以下名称均位于 `MarketCrash` namespace，路径相对 `formal/lean/MarketCrash/`。它们是基础引理，不是对整篇论文或整项结果的替代证明。

| 文件与 Lean 名称 | 论文对应 | 实际覆盖与限制 |
|---|---|---|
| `Definitions.lean:13–24`：`positivePrices`, `Response`, `coordinate`, `coordinateImage` | `paper/main.tex:74,127–135` | 严格正价格域、连续正响应和积分坐标；尚无完整 admissible path 定义。Response 的连续性已足够当前一阶积分引理；曲率另行假设可微性。 |
| `Coordinates.lean:7–37`：`coordinate_at_benchmark`, `coordinate_hasDerivAt`, `coordinate_strictMonoOn`, `normalized_trade_coefficient` | `paper/main.tex:127` | 坐标归一化、导数、正域严格单调、边际交易系数恒等式；未从价格控制方程推导路径链式法则。 |
| `Coordinates.lean:39–51`：`coordinate_unique` | `paper/main.tex:127` | 在正域、归一化及指定导数交易系数假设下唯一；不是任何未给定交易协议下的无条件唯一性。 |
| `Coordinates.lean:53–66`：`inverseOnImage`, `inverseOnImage_spec`, `inverseOnImage_left` | `paper/main.tex:129–135` | 仅在实际坐标像子类型上选取逆并证明对应；未证明逆的连续、可微或可达性等价。 |
| `Conservation.lean:8–25`：`paired_column_sum`, `ones_transpose_paired`, `trading_sum_zero`, `paired_trading_sum_zero` | `paper/main.tex:87,133,175–178` | 有限配对网络的代数列和与交易输入总和为零；边集任意，rates 可为任意实数，不是论文完整双向图、非负交易流的完整模型。 |
| `Conservation.lean:27–31`：`pulse_preserves_potential` | `paper/main.tex:105,175–180` | 抽象实坐标增量保持总和；未证明脉冲中间价格正性、坐标像约束或执行可行性。 |
| `Conservation.lean:33–44`：`normal_form_sum_derivative` | `paper/main.tex:129–135,175–178` | 假设各坐标路径已满足法向方程，证明总和导数；R 是任意函数，尚未定义或连接论文具体恢复函数，也未证明整个时间区间上的常量守恒。 |
| `ResponseFamilies.lean:6–50`：`constantCoordinate`, `linearCoordinate`, `logarithmicCoordinate`；`constantResponse`, `linearResponse`, `quadraticResponse`；三个 `*Coordinate_normalized` 和三个 `*Coordinate_hasDerivAt` | `paper/main.tex:219–234` | p=0、1、2 的闭式、归一化与导数。部分代数引理允许更宽参数域，连接到市场解释时仍使用正 F、正 η、正 S。 |
| `ResponseFamilies.lean:52–85`：`constantCoordinate_eq_integral`, `linearCoordinate_eq_integral`, `logarithmicCoordinate_eq_integral` | `paper/main.tex:229–234` | 三种闭式与原积分坐标在正域一致，不仅是未连接的公式。 |
| `ResponseFamilies.lean:87–157`：`constantCoordinate_lower_bound`, `constantCoordinate_range`, `constantCoordinate_image`, `linearCoordinate_lower_bound`, `linearCoordinate_range`, `linearCoordinate_image`, `logarithmicCoordinate_range`, `logarithmicCoordinate_image` | `paper/main.tex:135` | p=0、1、2 的确切坐标像；没有任意实数 p 或 p>2 分支。 |
| `Curvature.lean:6–17`：`responseElasticity`, `coordinate_slope_hasDerivAt`, `coordinate_slope_elasticity` | `paper/main.tex:181–188` | 证明 S/g(S) 的导数与弹性恒等式；未封装 Φ 二阶导数定理及全域凹性。 |
| `Curvature.lean:19–37`：`logCoordinate`, `logCoordinate_hasDerivAt`, `log_slope_hasDerivAt` | `paper/main.tex:185–188` | 对数复合坐标的一阶导数，以及其斜率导数恒等式；未完成全域凹性、Jensen 或障碍定理。 |

## 历史记录：Stage-1 整项结果边界

上表三个响应族的名称完整展开为：`constantCoordinate_normalized`, `linearCoordinate_normalized`, `logarithmicCoordinate_normalized`, `constantCoordinate_hasDerivAt`, `linearCoordinate_hasDerivAt`, `logarithmicCoordinate_hasDerivAt`。这些声明的名称与作用均直接来自对应 Lean 源码。

`docs/MATHEMATICAL_RESULTS.md` 中的符号检查、普通 ODE、离散抽样或精确有理数一致性检查，均不自动成为 Lean 证明。Stage-1 历史快照当时尚无整项 Lean 验收；随后曾完成 7.1、7.5、6.1；最终16/16状态以唯一当前入口为准。

Stage-1 历史快照当时：Proposition 7.6 的整项状态为外部 Python 严格区间计算机辅助存在性证明，未在 Lean 中重建或核验。它限于指定十资产、九目标、两日固定路径；不证明最优控制、一般异质市场可行性或真实市场概率。当时 Lean 不包含区间 ODE 证书检查器；此限制已由D01正式检查器及其健全性证明解除。`AxiomAudit.lean` 的打印命令只检查所列基础声明的依赖，不检查外部证书。

## 历史记录：Stage-1 后续障碍与下一步

1. 后续提交继续运行 kernel 构建与全部声明 axiom 审计；两者分开验收。
2. 定义实际恢复函数、正价格受控路径、非负配对美元流和 flow-completed 脉冲；连接价格方程、坐标方程及逆映射，证明全过程正性与像内约束。
3. 从当前斜率导数引理建立二阶导数、全域凹性、恢复比较与 Jensen 论证，才有条件推进 Theorem 3.1/3.2。
4. 单独处理一般 p 的坐标范围、局部 Taylor 展开与余项、有限资源构造、变差账本和滚动价格带；现有三个响应特例不能代替这些步骤。
5. 对 7.6 另行设计可信的有理数及区间 ODE 验证接口。外部证书成功不等于 Lean 核已检查证书。

本阶段 76 项 Lean 声明通过 kernel 与 axiom 审计；有限正则物理模型已证明 3.1/3.2 对应结论。原论文完整有限变差 admissibility 的等价和整项定理仍待形式化。
