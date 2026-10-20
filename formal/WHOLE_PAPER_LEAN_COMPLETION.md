# Original-result formal acceptance evidence

Original-result acceptance / 当前验收 **16/16**. This marker is read by the existing integrity checker.

Historical original-paper acceptance: 16/16 substantive numbered results. Theorem 1.1 is an informal overview, not a seventeenth result. The source baseline is `paper/main.tex`, with the Proposition 7.5 boundary correction documented in A01_SCOPE_AUDIT.md. Exact Lean quantifiers and assumptions govern scope.

Accepted proof-source commit: `15bec0e04613c040489b71a93595861ae5c82343`. Historical full build and 1,224-declaration audit are recorded in [FINAL_AXIOM_AUDIT.json](FINAL_AXIOM_AUDIT.json). Recorded same-commit workflows: [translations](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033132044), [SIAM](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39033082716), [reproducibility](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828360), [Lean](https://github.com/Siyuan-chat/market-crash-reachability/actions/runs/39032828458).

The later removal of `SmoothMarket`, `WeakBVFiniteExecution` and `WeakBVOriginalCrisis` preserved all canonical families and reported a 1,211-theorem local kernel/axiom audit. The historical JSON describes the earlier library, not the changed declaration count. This documentation revision does not imply a new local Lean build.

V14's five additions are outside this acceptance. No independent external proof audit is inferred from internal source review or CI. See the [manifest](ORIGINAL_RESULT_MANIFEST.md) and [current evidence matrix](../docs/RESULTS_AND_EVIDENCE.md).

## Historical result acceptance matrix

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
