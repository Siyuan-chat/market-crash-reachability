# Lean 全文验收清单与剩余工作（2026-10-17）

当前验收 **9/16**，目标 **16/16**。B06 Theorem 7.3 PAPER_ACCEPTED；证明 SHA `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；本地全量构建、436项公理审计和255项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980258)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980348)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980253)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980257)。 C01完整三脉冲及公共uniform余项已全量构建PASS，500项公理审计及264项发布哈希PASS，待同SHA四项CI；C02完整候选本地编译通过，待串行集成。C03连续控制、C04精确二次上界及可达阶数、D01核验证checker继续实现。运行目录 `phase4-execution`；本入口单写入。

**权威原文**：English V12 Final，见 `paper/main.tex`；具体原文映射见 [THEOREM_MAP.md](THEOREM_MAP.md)。**源代码证明范围以 Lean 定理的精确量词与假设为准，不能以声明总数量代替全文完成度。**

> **2026-10-16 direct-proof priority update:** [DIRECT_PAPER_PROOF_ROUTE.md](DIRECT_PAPER_PROOF_ROUTE.md) replaces the previously suggested requirement to solve arbitrary countably-atomic completed graphs as a prerequisite to Theorems 3.1/3.2. The original paper M5 allows only finitely many instantaneous flow-completed pulses. The genuine bridge is now locally proved in PhysicalBVNormalForm and the finite original economic trace, with original-input packaging; B02 final audit and same-SHA CI remain pending. The wider general-BV extensions remain optional. The exact endpoint Proposition 7.1 has now passed the matching Lean kernel and axiom audit; the current acceptance count and remaining numbered results are recorded above.

## 严格完成定义

- **基础声明（kernel-certified local result）**：固定 Lean 4.19/Mathlib 下 `lake build` 通过；逐条 `#print axioms` 只允许 `propext`、`Classical.choice`、`Quot.sound`；无 `sorry`、`admit` 或自定义 `axiom`。
- **全文某一结果完成（full original-result gate）**：Lean 结果覆盖原始论文定理的所有显式量词、响应函数/价格域/预算/库存/时间与终端资金闭合条件；具备从原始 M1–M5 模型到形式化路径的忠实连接，而不是额外强化条件的受限子类；需要存在性、最优上确界或数值证明的结果，必须分别验证这些构造与证书。
- **全文完成（whole-paper gate）**：全部 **16 项实质性编号 Theorem/Proposition** 的原文陈述各有可审计 Lean 验收。Theorem 1.1 为非正式综述，不作为独立第 17 项重复计数。

## 已确认的检查点

- PR #9 合入 `main`：**159** 项辅助与受限模型 Lean 定理通过完整审计。
- Draft PR #10，数学源码 SHA `7eeea5902707711413416eee13ef7830021d2df5`：**185/185** 项通过固定工具链与公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38865912687)。包括严格的有序原子执行、各资产 Stieltjes 结算恒等式及可数原子时刻。
- 新增 `CountablePhysicalClosure.lean`，数学提交 `5b182d74b35e525af108091510a7efc6edfc5103`：**190/190** 条声明通过 Lean kernel 和完整公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38867686935)。从真实可行的有限物理执行前缀、逐资产正价格收敛，严格推出极限势函数保持、全资产下降排除及系统危机排除；**仍需额外证明每条原始 M1–M5 BV 路径存在这种忠实物理前缀逼近**。
- **按原论文完整定理验收：目前 9/16（逐项名单及证明SHA见下表）**。原文的 k=⌈αN⌉<N、0<r<1、D∈ℕ、δ>0、正终端价格、精确补偿资产价格乘积充要条件、两种精确 Qα 条件和单补偿资产推论均由 Lean 证实。核心全量词定理 `proposition_7_1_original_endpoint`，附 `proposition_7_1_single_compensator`；[197/197 核心 Lean 与公理审计](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38983955426)。此为条件性终端恒等式，不主张所指定价格配置存在物理可行交易路径。其余7项尚未验收。

## 逐项结果矩阵

| 原文编号 | 关键数学对象或目标 | 当前整项 Lean 状态 | 下一关键义务 |
|---|---|---|---|
| Theorem 3.1 | 所有M1–M5路径、真实可达价格及任意时刻的全资产下降屏障 | **PAPER_ACCEPTED** | `dbb5c784b07b6f8fc5ec3738410346fffc7cc47c`；完整定理 `theorem_3_1_original`及四项同SHA CI通过，见 B02_SCOPE_AUDIT.md |
| Theorem 3.2 | 任意市场宽度、任意时刻的系统危机排除 | **PAPER_ACCEPTED** | `e80b03c0431ab0a8de444931f96ffa037e2b68f2`；完整 `theorem_3_2_original`及四项同SHA CI通过，见 B03_SCOPE_AUDIT.md |
| Theorem 4.1 | p=2/1/0 的 A/B/C 不可达、有限库存界与任意严重性可达 | 未完成 | B、C 的具体物理控制存在性、库存、预算独立界 |
| Proposition 4.2 | e(F)<1 的三脉冲共同下跌及精确渐近 | **LEAN_PASS，待同SHA CI** | 完整 `proposition_4_2_original_uniform`；全量构建、500项公理审计和264项哈希PASS，见 C01_SCOPE_AUDIT.md |
| Proposition 4.3 | e(F)<2 的双脉冲部分覆盖与二阶系数 | 未完成 | 双脉冲和终端闭合、渐近/危机覆盖 |
| Theorem 4.4 | 常数冲击下全覆盖的尖锐时间界及不取得的上确界 | 未完成 | 普适上界 + 任意低于临界值的构造序列 |
| Theorem 5.1 | 实际美元/净份额卖出/逐资产库存必要下界 | **PAPER_ACCEPTED** | `a1415e9745b65581a3c3053cc45be56c3763181c`；完整 `theorem_5_1_original`及四项同SHA CI通过，见 B04_SCOPE_AUDIT.md |
| Proposition 6.1 | 速率+价格带下界及必要交易速度 | **PAPER_ACCEPTED** | `de95f967b533794677012281432b401aab4517b3`；三个 canonical 分支及四项同 SHA CI 全绿，见 A02_SCOPE_AUDIT.md |
| Theorem 6.2 | 常数冲击下全宽度二次小速率上界 | 未完成 | 统一小速率估计、常数严格性 |
| Theorem 6.3 | 有连续速率及股数、价格带约束的实际下跌构造 | 未完成 | 连续正则控制的构造、零终端账本与预算 |
| Proposition 7.1 | 多日条件式终端危机触发、两种精确分位数情形及单补偿资产推论 | **已完成；197声明核审计通过** | 原文条件性终端命题已完整覆盖；不等同于动态交易路径存在性 |
| Proposition 7.2 | 逐日涨跌停与速度的必需条件 | **PAPER_ACCEPTED** | 5c84995094b736c0231df6d804c8daad638bbfc7；完整三分支、原文范围审查及四项同 SHA CI 通过；见 A03_SCOPE_AUDIT.md |
| Theorem 7.3 | 异质资产第二日全资产共同再下跌排除 | **PAPER_ACCEPTED** | `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；完整 `theorem_7_3_original`及四项同SHA CI通过，见 B06_SCOPE_AUDIT.md |
| Proposition 7.4 | 闭合美元账本下的多日预处理必要量 | **PAPER_ACCEPTED** | `131256911c0d21ff837a477cc63c8241ebcb27c7`；完整 `proposition_7_4_original`及四项同SHA CI通过，见 B05_SCOPE_AUDIT.md |
| Proposition 7.5 | 市场割集成交能力/速率限制 | **PAPER_ACCEPTED** | `772d72d6c3b819814ce39a165a1bb56ad6729ee6`；四项同 SHA CI 成功，完整定理族及量词映射见 A01_SCOPE_AUDIT.md |
| Proposition 7.6 | N=10、两日严格区间证书的有界连续控制存在性 | 未完成；仅存在**外部 Python 区间认证** | 将实际证书、计算闭包及所有区间判定纳入 Lean 或验证型 checker |

## 当前执行状态

1. B01 非编号桥接：真实连续 BV 物理价格/份额/美元 primitive → operational ODE → nonlinear normal form 全部本地编译通过，包含 singular-continuous 控制。原始单边 [0,z] 脉冲归一化及有限区间 Stieltjes 延拓也已 kernel 验证。
2. B02 Theorem 3.1：B02 Theorem 3.1 PAPER_ACCEPTED；证明 SHA `dbb5c784b07b6f8fc5ec3738410346fffc7cc47c`；本地完整构建、360项公理审计及245项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617907)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617901)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617894)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617891)。
3. B03 Theorem 3.2：B03 Theorem 3.2 PAPER_ACCEPTED；证明 SHA `e80b03c0431ab0a8de444931f96ffa037e2b68f2`；本地全量构建、362项公理审计及247项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188459)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188372)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188404)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188355)。
4. B04 Theorem 5.1：B04 Theorem 5.1 PAPER_ACCEPTED；证明 SHA `a1415e9745b65581a3c3053cc45be56c3763181c`；本地全量构建、413项公理审计及251项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767964)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767913)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768014)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768057)。
5. B05 Proposition 7.4：B05 Proposition 7.4 PAPER_ACCEPTED；证明 SHA `131256911c0d21ff837a477cc63c8241ebcb27c7`；本地全量构建、433项公理审计和253项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405730)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405801)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405755)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405739)。
6. B06 Theorem 7.3 PAPER_ACCEPTED；证明 SHA `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；本地全量构建、436项公理审计和255项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980258)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980348)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980253)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980257)。
7. C01–C06、D01 尚未通过原文验收；数值区间证书仍需 Lean soundness 和真实物理构造，不以既有 Python 通过替代。

当前没有已授权自动续办或脱离工具管理的后台任务。检查点为本工作分支及此单一入口；本地工具会话仅用于当前构建/审计。

**工程纪律**：不改 English V12 Final 的数学主张；不暗中增加模型定理所需假设；所有结论必须标注 exact-SHA CI；独立严格区间证书不得因 Python 测试通过而标成 Lean-checked；PR #10 维持 Draft，除非经过专门审查。
