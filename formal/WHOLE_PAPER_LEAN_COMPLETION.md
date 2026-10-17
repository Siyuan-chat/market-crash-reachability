# Lean 全文验收清单与剩余工作（2026-10-17）

当前验收 **2/16**，目标 **16/16**。A01 Proposition 7.5 **PAPER_ACCEPTED**，完整证明提交 `772d72d6c3b819814ce39a165a1bb56ad6729ee6` 的四项 CI 全部 SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704394)；[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704369)；[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704465)；[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704392)。本地全量构建、228项公理审计、226项发布哈希、六项数值回归与译本/SIAM检查通过。A02 Proposition 6.1 **LEAN_PASS**（全量本地构建及245项公理审计通过，待同最新提交 CI）；A03 完整证明候选已编译，待串行整合；B01 正推进原始物理 BV 换元投影，不计编号结果。用户明确批准的 A01 非空 J、非空接收侧分母及 m>0 边界修正见 [A01_SCOPE_AUDIT.md](A01_SCOPE_AUDIT.md)，其余数学主张未改。运行目录 `phase4-execution`，指定分支、Lean 4.19.0；本入口单写入记录当前状态。

**权威原文**：English V12 Final，见 `paper/main.tex`；具体原文映射见 [THEOREM_MAP.md](THEOREM_MAP.md)。**源代码证明范围以 Lean 定理的精确量词与假设为准，不能以声明总数量代替全文完成度。**

> **2026-10-16 direct-proof priority update:** [DIRECT_PAPER_PROOF_ROUTE.md](DIRECT_PAPER_PROOF_ROUTE.md) replaces the previously suggested requirement to solve arbitrary countably-atomic completed graphs as a prerequisite to Theorems 3.1/3.2. The original paper M5 allows only finitely many instantaneous flow-completed pulses. The **remaining genuine bridge** is primitive M2 physical marginal settlement → integrated weak-normal-form law for every admissible continuous finite-variation execution piece, followed by finite physical concatenation. The wider general-BV extensions remain optional. The exact endpoint Proposition 7.1 has now passed the matching Lean kernel and axiom audit; the other fifteen statements remain open.

## 严格完成定义

- **基础声明（kernel-certified local result）**：固定 Lean 4.19/Mathlib 下 `lake build` 通过；逐条 `#print axioms` 只允许 `propext`、`Classical.choice`、`Quot.sound`；无 `sorry`、`admit` 或自定义 `axiom`。
- **全文某一结果完成（full original-result gate）**：Lean 结果覆盖原始论文定理的所有显式量词、响应函数/价格域/预算/库存/时间与终端资金闭合条件；具备从原始 M1–M5 模型到形式化路径的忠实连接，而不是额外强化条件的受限子类；需要存在性、最优上确界或数值证明的结果，必须分别验证这些构造与证书。
- **全文完成（whole-paper gate）**：全部 **16 项实质性编号 Theorem/Proposition** 的原文陈述各有可审计 Lean 验收。Theorem 1.1 为非正式综述，不作为独立第 17 项重复计数。

## 已确认的检查点

- PR #9 合入 `main`：**159** 项辅助与受限模型 Lean 定理通过完整审计。
- Draft PR #10，数学源码 SHA `7eeea5902707711413416eee13ef7830021d2df5`：**185/185** 项通过固定工具链与公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38865912687)。包括严格的有序原子执行、各资产 Stieltjes 结算恒等式及可数原子时刻。
- 新增 `CountablePhysicalClosure.lean`，数学提交 `5b182d74b35e525af108091510a7efc6edfc5103`：**190/190** 条声明通过 Lean kernel 和完整公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38867686935)。从真实可行的有限物理执行前缀、逐资产正价格收敛，严格推出极限势函数保持、全资产下降排除及系统危机排除；**仍需额外证明每条原始 M1–M5 BV 路径存在这种忠实物理前缀逼近**。
- **按原论文完整定理验收：目前 2/16（Proposition 7.1、7.5）**。原文的 k=⌈αN⌉<N、0<r<1、D∈ℕ、δ>0、正终端价格、精确补偿资产价格乘积充要条件、两种精确 Qα 条件和单补偿资产推论均由 Lean 证实。核心全量词定理 `proposition_7_1_original_endpoint`，附 `proposition_7_1_single_compensator`；[197/197 核心 Lean 与公理审计](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38983955426)。此为条件性终端恒等式，不主张所指定价格配置存在物理可行交易路径。其余14项尚未验收。

## 逐项结果矩阵

| 原文编号 | 关键数学对象或目标 | 当前整项 Lean 状态 | 下一关键义务 |
|---|---|---|---|
| Theorem 3.1 | 所有 M1–M5 路径的全资产共同下跌屏障，弹性仅限可达价格 | 未完成；有限物理路径的类比证明已验证 | 全 BV 路径表示、无条件 a.e. FTC、可达价格局部化 |
| Theorem 3.2 | 任意市场宽度、任意时刻的系统危机排除 | 未完成；危机分位数与正则物理路径已证明 | 同上，尤其全路径对数坐标凹性与原价域一致 |
| Theorem 4.1 | p=2/1/0 的 A/B/C 不可达、有限库存界与任意严重性可达 | 未完成 | B、C 的具体物理控制存在性、库存、预算独立界 |
| Proposition 4.2 | e(F)<1 的三脉冲共同下跌及精确渐近 | 未完成 | 三脉冲构造、Taylor 控制、全物理条件 |
| Proposition 4.3 | e(F)<2 的双脉冲部分覆盖与二阶系数 | 未完成 | 双脉冲和终端闭合、渐近/危机覆盖 |
| Theorem 4.4 | 常数冲击下全覆盖的尖锐时间界及不取得的上确界 | 未完成 | 普适上界 + 任意低于临界值的构造序列 |
| Theorem 5.1 | 正一般 g 下交易美元/出售股份/库存的必要下界 | 未完成 | BV 价格与份额微分的积分资源证明 |
| Proposition 6.1 | 速率+价格带下界及必要交易速度 | **LEAN_PASS，待同最新提交完整 CI** | 三个 canonical 分支均覆盖，见 A02_SCOPE_AUDIT.md；尚未计入接受数 |
| Theorem 6.2 | 常数冲击下全宽度二次小速率上界 | 未完成 | 统一小速率估计、常数严格性 |
| Theorem 6.3 | 有连续速率及股数、价格带约束的实际下跌构造 | 未完成 | 连续正则控制的构造、零终端账本与预算 |
| Proposition 7.1 | 多日条件式终端危机触发、两种精确分位数情形及单补偿资产推论 | **已完成；197声明核审计通过** | 原文条件性终端命题已完整覆盖；不等同于动态交易路径存在性 |
| Proposition 7.2 | 逐日涨跌停与速度的必需条件 | 未完成 | 滚动边界与速率比较 |
| Theorem 7.3 | 第二交易日全资产再次共同跌停的阻碍 | 未完成 | 跨日物理势函数/结算约束 |
| Proposition 7.4 | 连续跌停需要的预处理量 | 未完成 | 路径资源及跨日价位不等式 |
| Proposition 7.5 | 市场割集成交能力/速率限制 | **PAPER_ACCEPTED** | `772d72d6c3b819814ce39a165a1bb56ad6729ee6`；四项同 SHA CI 成功，完整定理族及量词映射见 A01_SCOPE_AUDIT.md |
| Proposition 7.6 | N=10、两日严格区间证书的有界连续控制存在性 | 未完成；仅存在**外部 Python 区间认证** | 将实际证书、计算闭包及所有区间判定纳入 Lean 或验证型 checker |

## 核心逻辑关键路径（先完成 3.1/3.2）

1. **原始 BV 交易控制 → 完成图**：包含物理时间、Singular-continuous 部分以及有序可数原子跳跃；忠实保留真实价格、库存与逐资产资金状态。当前仅有真实 Stieltjes 资金度量、局部物理脉冲与有限有序跳跃，尚无面向所有原始控制的存在/覆盖定理。
2. **真实物理价格动力学 → a.e. 有效方程**：已有 `AEOperationalClockSegment` 的条件化物理 a.e. 价格/交易 ODE 及由它导出的坐标链式法则；缺少所有原始路径都满足该类型的证明。
3. **无条件绝对连续 FTC**：证明 `J(u)=exp(ρt(u))Σ_iΦ(S_i(u))` 的绝对连续性与 `∫J'=J(b)-J(a)`。目前端点势函数屏障仍要显式额外提供这一恒等式；没有这一步，a.e. 导数非负不足以推出端点保持。
4. **完整可达价格局部化**：沿任意完成图验证区间价位实际可达（含内部跳跃点），并将 3.1 的 `e≥1`、3.2 的 `e≥2` 限定在论文原本的 admissible price range。
5. **原始全量词升级验收**：完整 M1–M5 约束、任意时间、任意参数下逐项证明 3.1/3.2；之后把 14 项独立结果分组成构造性证明（§4、§6.3）、资源上界（§5–6）、多日限制与严格计算证书（§7）逐项完成。

**结论**：验证的数学基础已积累，但按 *full original theorem* 的严格验收，目前不可给出可信的完成百分比，也不应仅由 185 项辅助证明推断剩余工作量较小。已首次完成一项原始编号结果；下一步应按逐项原文验收路径推进其余 15 项，而非增加外围引理。

**工程纪律**：不改 English V12 Final 的数学主张；不暗中增加模型定理所需假设；所有结论必须标注 exact-SHA CI；独立严格区间证书不得因 Python 测试通过而标成 Lean-checked；PR #10 维持 Draft，除非经过专门审查。
