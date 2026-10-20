# Lean 全文验收清单与证据（2026-10-17）

## 当前维护：2026-10-20 冗余模块清理

用户授权移除 `SmoothMarket`、`WeakBVFiniteExecution`、`WeakBVOriginalCrisis`
三个已由原始物理路径证明取代且不再被编号结果依赖的历史模型模块；同步移除
总入口的三条导入及十三条公理审计项。原始十六项 canonical proof families 保留，
V14 新增结果不在本次清理范围内。

本次固定 Lean 4.19.0/Mathlib 完整本地构建 PASS；1211 条定理的 kernel/axiom 审计 PASS，十六项 canonical proof families 全部保留，无未完成证明或额外公理。
下文 1224 条声明与原证明 SHA 的记录，以及 `FINAL_AXIOM_AUDIT.json`，均为保留的
历史验收证据。清理变更提交后的精确 SHA 与 GitHub CI 结果由对应维护 PR 记录。
本地维护证据包括完整构建、公理审计、发布清单检查及修改前备份。

当前验收 **16/16**，目标 **16/16** 已达成。D01 Proposition 7.6 PAPER_ACCEPTED；证明 SHA `15bec0e04613c040489b71a93595861ae5c82343`；本地完整构建、1224项公理审计PASS；四项同SHA CI SUCCESS：[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033132044)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033082716)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828360)、[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828458)。本次不另列SHA-256验收门（用户最新决定）。 全部原始编号结果的量词与物理模型范围见下表及各项审查。PR #10保持Draft；本入口单写入。

**权威原文**：English V12 Final，见 `paper/main.tex`；具体原文映射见 [THEOREM_MAP.md](THEOREM_MAP.md)。**源代码证明范围以 Lean 定理的精确量词与假设为准，不能以声明总数量代替全文完成度。**

> **Historical 2026-10-16 direct-proof priority update (superseded by the 16/16 matrix):** [DIRECT_PAPER_PROOF_ROUTE.md](DIRECT_PAPER_PROOF_ROUTE.md) replaces the previously suggested requirement to solve arbitrary countably-atomic completed graphs as a prerequisite to Theorems 3.1/3.2. The original paper M5 allows only finitely many instantaneous flow-completed pulses. The genuine bridge is now locally proved in PhysicalBVNormalForm and the finite original economic trace, with original-input packaging; B02 final audit and same-SHA CI remain pending. The wider general-BV extensions remain optional. The exact endpoint Proposition 7.1 has now passed the matching Lean kernel and axiom audit; the current acceptance count and remaining numbered results are recorded above.

## 严格完成定义

- **基础声明（kernel-certified local result）**：固定 Lean 4.19/Mathlib 下 `lake build` 通过；逐条 `#print axioms` 只允许 `propext`、`Classical.choice`、`Quot.sound`；无 `sorry`、`admit` 或自定义 `axiom`。
- **全文某一结果完成（full original-result gate）**：Lean 结果覆盖原始论文定理的所有显式量词、响应函数/价格域/预算/库存/时间与终端资金闭合条件；具备从原始 M1–M5 模型到形式化路径的忠实连接，而不是额外强化条件的受限子类；需要存在性、最优上确界或数值证明的结果，必须分别验证这些构造与证书。
- **全文完成（whole-paper gate）**：全部 **16 项实质性编号 Theorem/Proposition** 的原文陈述各有可审计 Lean 验收。Theorem 1.1 为非正式综述，不作为独立第 17 项重复计数。

## 已确认的检查点

- PR #9 合入 `main`：**159** 项辅助与受限模型 Lean 定理通过完整审计。
- Draft PR #10，数学源码 SHA `7eeea5902707711413416eee13ef7830021d2df5`：**185/185** 项通过固定工具链与公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38865912687)。包括严格的有序原子执行、各资产 Stieltjes 结算恒等式及可数原子时刻。
- 新增 `CountablePhysicalClosure.lean`，数学提交 `5b182d74b35e525af108091510a7efc6edfc5103`：**190/190** 条声明通过 Lean kernel 和完整公理审计；[成功 CI](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/38867686935)。从真实可行的有限物理执行前缀、逐资产正价格收敛，严格推出极限势函数保持、全资产下降排除及系统危机排除；**仍需额外证明每条原始 M1–M5 BV 路径存在这种忠实物理前缀逼近**。
- **按原论文完整定理验收：16/16**，逐项名单、精确证明SHA、量词及CI证据见下表。

## 逐项结果矩阵

既有 Proposition 7.1 的中文旧状态现统一为 `PAPER_ACCEPTED`，不增加原始结果计数。其 `CrisisQuantile.lean` 从证明提交 `2141479f3eb7609c9f3fd13773c07cb7219378ad` 到共同复核提交 `772d72d6c3b819814ce39a165a1bb56ad6729ee6` 无差异；后者的 [Lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704394)、[复现](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704369)、[SIAM](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704465)、[翻译](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39010704392) 均已重新核实成功。早期证明提交本身的失败CI不作为通过证据。

| 原文编号 | 关键数学对象或目标 | 当前整项 Lean 状态 | 已闭合义务与证据 |
|---|---|---|---|
| Theorem 3.1 | 所有M1–M5路径、真实可达价格及任意时刻的全资产下降屏障 | **PAPER_ACCEPTED** | `dbb5c784b07b6f8fc5ec3738410346fffc7cc47c`；完整定理 `theorem_3_1_original`及四项同SHA CI通过，见 B02_SCOPE_AUDIT.md |
| Theorem 3.2 | 任意市场宽度、任意时刻的系统危机排除 | **PAPER_ACCEPTED** | `e80b03c0431ab0a8de444931f96ffa037e2b68f2`；完整 `theorem_3_2_original`及四项同SHA CI通过，见 B03_SCOPE_AUDIT.md |
| Theorem 4.1 | p=2/1/0 的 A/B/C 不可达、有限库存界与任意严重性可达 | **PAPER_ACCEPTED** | `37e9c89c106cd85735ff2a500a922f32802f8d15`；完整ABC `theorem_4_1_original`、量词审查及四项同SHA CI通过，见 C06_SCOPE_AUDIT.md |
| Proposition 4.2 | e(F)<1 的三脉冲共同下跌及精确渐近 | **PAPER_ACCEPTED** | `c58a3287c94d3bcc56386a7715657fad489ec8be`；完整 `proposition_4_2_original_uniform`及四项同SHA CI通过，见 C01_SCOPE_AUDIT.md |
| Proposition 4.3 | e(F)<2 的双脉冲部分覆盖与二阶系数 | **PAPER_ACCEPTED** | `e28dc8bb9eb415be3974a947aae7e4bc6361c7d3`；完整 `proposition_4_3_original`及四项同SHA CI通过，见 C02_SCOPE_AUDIT.md |
| Theorem 4.4 | 常数冲击下全覆盖的尖锐时间界及不取得的上确界 | **PAPER_ACCEPTED** | `74f023fc5d129cebeb9874f5fe7c35b663029d3d`；完整 `theorem_4_4_original`及四项同SHA CI通过，见 C05_SCOPE_AUDIT.md |
| Theorem 5.1 | 实际美元/净份额卖出/逐资产库存必要下界 | **PAPER_ACCEPTED** | `a1415e9745b65581a3c3053cc45be56c3763181c`；完整 `theorem_5_1_original`及四项同SHA CI通过，见 B04_SCOPE_AUDIT.md |
| Proposition 6.1 | 速率+价格带下界及必要交易速度 | **PAPER_ACCEPTED** | `de95f967b533794677012281432b401aab4517b3`；三个 canonical 分支及四项同 SHA CI 全绿，见 A02_SCOPE_AUDIT.md |
| Theorem 6.2 | 常数冲击下全宽度精确二次小速率上界、可达阶与最小速率Theta | **PAPER_ACCEPTED** | `e0196b317f0fb752d715fdfadfe9c9ba9faae698`；完整 `theorem_6_2_original`及四项同SHA CI通过，见 C04_SCOPE_AUDIT.md |
| Theorem 6.3 | 有连续速率及股数、价格带约束的实际下跌构造 | **PAPER_ACCEPTED** | `937f8d2e1bb5a2556abeb793ab6aaca723b5ddf5`；完整 `theorem_6_3_original`及四项同SHA CI通过，见 C03_SCOPE_AUDIT.md |
| Proposition 7.1 | 多日条件式终端危机触发、两种精确分位数情形及单补偿资产推论 | **PAPER_ACCEPTED** | 既有完整基线；`proposition_7_1_original_endpoint`及`proposition_7_1_single_compensator`，共同复核SHA `772d72d6c3b819814ce39a165a1bb56ad6729ee6` 四项CI通过；条件性终端命题，不主张指定端点的路径存在性 |
| Proposition 7.2 | 逐日涨跌停与速度的必需条件 | **PAPER_ACCEPTED** | 5c84995094b736c0231df6d804c8daad638bbfc7；完整三分支、原文范围审查及四项同 SHA CI 通过；见 A03_SCOPE_AUDIT.md |
| Theorem 7.3 | 异质资产第二日全资产共同再下跌排除 | **PAPER_ACCEPTED** | `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；完整 `theorem_7_3_original`及四项同SHA CI通过，见 B06_SCOPE_AUDIT.md |
| Proposition 7.4 | 闭合美元账本下的多日预处理必要量 | **PAPER_ACCEPTED** | `131256911c0d21ff837a477cc63c8241ebcb27c7`；完整 `proposition_7_4_original`及四项同SHA CI通过，见 B05_SCOPE_AUDIT.md |
| Proposition 7.5 | 市场割集成交能力/速率限制 | **PAPER_ACCEPTED** | `772d72d6c3b819814ce39a165a1bb56ad6729ee6`；四项同 SHA CI 成功，完整定理族及量词映射见 A01_SCOPE_AUDIT.md |
| Proposition 7.6 | N=10、两日严格区间证书的有界连续控制存在性 | **PAPER_ACCEPTED** | `15bec0e04613c040489b71a93595861ae5c82343`；完整同路径 `proposition_7_6_original`、量词审查及四项同SHA CI通过，见 D01_SCOPE_AUDIT.md |

## 当前执行状态

1. B01 非编号桥接：真实连续 BV 物理价格/份额/美元 primitive → operational ODE → nonlinear normal form 全部本地编译通过，包含 singular-continuous 控制。原始单边 [0,z] 脉冲归一化及有限区间 Stieltjes 延拓也已 kernel 验证。
2. B02 Theorem 3.1：B02 Theorem 3.1 PAPER_ACCEPTED；证明 SHA `dbb5c784b07b6f8fc5ec3738410346fffc7cc47c`；本地完整构建、360项公理审计及245项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617907)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617901)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617894)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39012617891)。
3. B03 Theorem 3.2：B03 Theorem 3.2 PAPER_ACCEPTED；证明 SHA `e80b03c0431ab0a8de444931f96ffa037e2b68f2`；本地全量构建、362项公理审计及247项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188459)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188372)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188404)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013188355)。
4. B04 Theorem 5.1：B04 Theorem 5.1 PAPER_ACCEPTED；证明 SHA `a1415e9745b65581a3c3053cc45be56c3763181c`；本地全量构建、413项公理审计及251项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767964)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013767913)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768014)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39013768057)。
5. B05 Proposition 7.4：B05 Proposition 7.4 PAPER_ACCEPTED；证明 SHA `131256911c0d21ff837a477cc63c8241ebcb27c7`；本地全量构建、433项公理审计和253项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405730)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405801)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405755)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014405739)。
6. B06 Theorem 7.3 PAPER_ACCEPTED；证明 SHA `d538dd345c33a1ad970463b23aa6a34d1b69be5a`；本地全量构建、436项公理审计和255项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980258)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980348)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980253)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39014980257)。
7. C01 Proposition 4.2 PAPER_ACCEPTED；证明 SHA `c58a3287c94d3bcc56386a7715657fad489ec8be`；本地全量构建、500项公理审计和264项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791535)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791496)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791519)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39015791505)。
8. C02 Proposition 4.3 PAPER_ACCEPTED；证明 SHA `e28dc8bb9eb415be3974a947aae7e4bc6361c7d3`；本地全量构建、502项公理审计和266项哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534598)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534620)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534597)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39016534616)。
9. C03 Theorem 6.3 PAPER_ACCEPTED；证明 SHA `937f8d2e1bb5a2556abeb793ab6aaca723b5ddf5`；本地完整构建、593项公理审计及269项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658676)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658720)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658705)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39018658632)。
10. C04 Theorem 6.2 PAPER_ACCEPTED；证明 SHA `e0196b317f0fb752d715fdfadfe9c9ba9faae698`；本地完整构建、615项公理审计及272项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39019425830)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39019425896)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39019425973)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39019425883)。
11. C05 Theorem 4.4 PAPER_ACCEPTED；证明 SHA `74f023fc5d129cebeb9874f5fe7c35b663029d3d`；本地完整构建、695项公理审计及281项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39020411221)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39020411126)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39020411114)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39020411156)。
12. C06 Theorem 4.1 PAPER_ACCEPTED；证明 SHA `37e9c89c106cd85735ff2a500a922f32802f8d15`；本地完整构建、787项公理审计及291项发布哈希PASS；四项同SHA CI SUCCESS：[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946468)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946511)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946465)、[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39021946461)。
13. D01 Proposition 7.6 PAPER_ACCEPTED；证明 SHA `15bec0e04613c040489b71a93595861ae5c82343`；本地完整构建、1224项公理审计PASS；四项同SHA CI SUCCESS：[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033132044)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033082716)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828360)、[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828458)。本次不另列SHA-256验收门（用户最新决定）。

当前没有已授权自动续办或脱离工具管理的后台任务。检查点为本工作分支及此单一入口；本地工具会话仅用于当前构建/审计。

**历史运行记录（已结束）**：暂停前 D01 正式模块预构建由工具会话 `24222` 管理：`lake build MarketCrash.RationalIntervalChecker MarketCrash.CertificateCoarseBootstrap MarketCrash.CertifiedRateLower`。冻结输入身份见 `build/formal/d01-prebuild-inputs.json`，完整输出/终态见 `build/formal/d01-official-prebuild/result.json`（文件尚未产生时不得当作通过）。这只准备正式 Lake 缓存，不增加原始编号验收数；最终八模块整合仍需完整构建和全量审计。

**工程纪律**：不改 English V12 Final 的数学主张；不暗中增加模型定理所需假设；所有结论必须标注 exact-SHA CI；独立严格区间证书不得因 Python 测试通过而标成 Lean-checked；PR #10 维持 Draft，除非经过专门审查。

## 历史暂停与恢复快照（已结束；不代表当前状态）

> 下列快照保留失败、暂停和恢复轨迹；当前终态以上方16/16矩阵及最终验收段落为准。

> ## 用户暂停检查点（2026-10-17）
>
> 用户明确要求保存进度后暂停。当前 **PAUSED_BY_USER**，原始编号验收仍 **15/16**；PR #10 保持 Draft，最新已推送提交 `37e9c89c106cd85735ff2a500a922f32802f8d15`。当前未提交改动与八份 D01 Working 源码保留，逐文件 SHA-256 和独立源码副本见 `build/formal/pause-20261017/checkpoint.json` 及同目录。
>
> D01 尚未验收：`canonical-tail2.exit=1`，额外可行集 infimum bracket 在 `<stdin>:812` 出现 `simp made no progress`，该失败声明的打印含 `sorryAx`，不得计为公理审计通过；原 `proposition_7_6_original` 打印仅标准三公理，但尚未完成冻结版全链验证。正式三模块预构建会话 `24222` 已按暂停要求中断、exit 1，PID 163472 已不在进程清单，不能计 PASS。旧资源编译已于 `2026-10-17T10:23:55Z` 终止、exit -1，原始记录 `build/formal/d01-resource-rows/full-kernel-run.json` 已收录检查点；最终进程复查没有剩余 Lean 进程（Get-Process 无匹配返回 exit 1）。两个中断构建均不计为通过。
>
> 恢复时从此入口读取，先处理上述唯一附加 bracket 编译错误；随后完成必要资源数据精简与生成器身份核对、八模块冻结整合、全库构建、公理清单更新与审计、发布 SHA-256 和同提交四项 CI；全部通过后才能更新为16/16。无自动续办授权。
>
> ## 恢复执行（2026-10-17）
>
> 用户已明确要求继续，先前暂停请求已撤销。当前主任务恢复 **IN_PROGRESS**，验收仍15/16。D01负责人恢复唯一附加 bracket 编译修复与冻结验证；主负责正式整合及全部验收门。暂停快照保留为历史恢复证据。
>
> **历史运行记录（已结束）**：当前恢复后的正式三模块预构建会话为 `83593`，输入仍为 `build/formal/d01-prebuild-inputs.json`，输出与终态为 `build/formal/d01-official-prebuild-resumed/result.json`；文件未产生时不计通过。
>
> D01恢复后 targeted canonical 编译已退出0（`build/formal/d01-resource-rows/resume-canonical.exit`），主命题及附加 bracket 的打印均仅标准三公理；旧 bracket simp错误已修复。现仍待必要资源数据精简后的冻结整链及正式全量验收，不增加15/16计数。
>
> **历史运行记录（已结束）**：恢复执行检查点：D01八份冻结源码已整合正式模块，局部437/437公理审计PASS；正式默认路径复现全部801检查点、末端201行及第40000行参考数据PASS（`build/formal/d01-official-reproduced-inputs/result.json`）。全库1224条声明已登记，发布清单303项。当前唯一计算为正式预构建工具会话83593（`build/formal/d01-official-prebuild-resumed/result.json` 未产生，故尚未PASS）；它结束后执行全库build、完整公理审计、最后哈希检查，提交并验证四项同SHA CI。原始编号验收保持15/16。
>
> 正式80,000步价格核验已退出0：`build/formal/d01-official-prebuild-resumed/result.json`，stdout SHA-256 `ac5bfce7eb053179aebfc8e4a77327e3760aefd66a7bf75097fd6769aba13428`。全项目构建16194已退出0，日志 `build/formal/d01-full-build/result.json`，stdout SHA-256 `cc1a51b4f2310f8a00600e3aea5d59ff2e9a3bdaa3e8e70d6291c0512a21ff6f`。当前实际全1224条公理审计会话87067（`build/formal/d01-integrity/result.json`）；D01尚未PAPER_ACCEPTED。
>

## 用户最新决定：取消单独哈希验收（2026-10-17）

用户明确要求“哈希检查去掉，没必要”。本次不再单独执行SHA-256验收，也不把它列为完成门槛；保留Lean完整编译、全部声明标准公理审计、原文量词核对及最新提交四项CI。仓库既有发布清单随现有CI维护；历史已完成的哈希记录保留为历史证据。输入数据的来源身份与同提交CI仍可追溯。

**历史运行记录（已结束）**：D01官方完整构建与全量公理审计均已PASS：1224条声明、无未完成证明或额外公理，审计 stdout SHA-256 `d0b63fdc29bd14188f7a16eb8500d54ccc3841ed27cd567d57c7a72a34530d15`。原编号状态升级LEAN_PASS，接受计数仍15/16；后续固定源码提交与四项同SHA CI。

## 原始编号结果全部验收

D01 Proposition 7.6 PAPER_ACCEPTED；证明 SHA `15bec0e04613c040489b71a93595861ae5c82343`；本地完整构建、1224项公理审计PASS；四项同SHA CI SUCCESS：[translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033132044)、[siam](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033082716)、[verify](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828360)、[lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828458)。本次不另列SHA-256验收门（用户最新决定）。
此前暂停、失败试验及运行记录保留为历史证据；当前完整范围与每项接受SHA以上表为准。更强的未编号数值界限不自动成为Lean已证明结论，D01精确范围见D01_SCOPE_AUDIT.md及D01_CERTIFICATE_PROVENANCE.md。
