# V20 Gate 3 第二轮数学与写作审计（2026-11-05）

**判定：实质推进，Gate 3 尚未清关。** 本轮只修改独立的 `submission/v20-gate3-activity-recovery/` 和 `research/v20-gate3/`，不修改原始 40 页稿、V16/V17、历史版本和 DOI。

## 1. 本轮新增且可独立检查的数学内容

| 原始 ID | 新论证/写作位置 | 内部证据等级 | 严格边界 |
|---|---|---|---|
| P12 | `prop:hetero-weighted`, `prop:hetero-two` | ANALYTIC_PROOF | `g_i(S)=η_i(S/F)^2`、`κ_i>0`、成对美元交易、事件内部恢复；异质性反例仅给出充分小交易量局部存在性，不等于全局异质相图 |
| P11 | `prop:unmatched`, `eq:crisis-robust` | ANALYTIC_PROOF (CONDITIONAL) | 未配对 `e_i(t)` 仅作单独扰动模型，**不**自动生成毛成交；固定同一成对边流、同一正紧致价格区间才有 Gronwall 界。终端闭账还需 `∫e_i=0` |
| L01 | `lem:one-sided-bv`, `app:bv` | ANALYTIC_PROOF | 取终点前最后一段价格低于 F 的轨迹；负变差与 C0 真正的毛卖股数不同，后者可大于前者 |
| A05 / T08 | `prop:rate-explicit`, `prop:rate-local-match`, `app:rates` | ANALYTIC_PROOF | `v C_I T < min(d,F/2)` 下显式二次上界；C1 九边三角通过顺序定额执行给出同阶局部下界，不推出严重损失的最优速率 |
| A07 / A03 | `lem:radial-general`, `lem:terminal-inventory`, `app:general-p` | ANALYTIC_IDENTITIES / PARTIAL | `ν=2-p>1` 的精确径向公式、库存可积性已证明；**尚未**完成每个固定 `0<p<1` 的端点异号/Jacobian/统一平滑根证明 |
| P10 / R03 | `cor:at-most-n-minus-one` | ANALYTIC_PROOF (NECESSARY BOUND) | 以全部资产首日 `1-ℓ` 下限价收盘为前提，次日上限 `(1-ℓ²)F<F`，由活动潜能单调性排除**所有 N 项**第二天再跌停。N=10 由已证五目标可达和新排除十目标得到 `5≤k*≤9`；不宣称 9 可达或旧“最多 7”有效 |
| B01 | `tab:analytic-severity`, `tab:reconstruction` | ANALYTIC_BOUND + NUMERIC_ONLY | δ=3/5/10/20 是新显式证书的**存在性级别**，q=e^(-2δ-5)，固定 M/H 上界；旧 h=.012 浮点轨迹没有升级为严格区间根 |

### 异质二次模型的非平凡反例

令 `D_i=F²/η_i`，`q_i=ln(S_i/F)`。事件金额作为时钟时 `dq_i/da=σ_i/D_i−κ_i(1−e^(−q_i))`。两笔等金额 z 的相反方向 C1 交易使两资产的净美元账目均精确为零。终点处 `q_i(2z)=−σ_i(κ_i/D_i)z²+O(z³)`，因此只要 `κ_1/D_1>κ_2/D_2`，就有 `C_{1/2}>0`（充分小 z）。这一反例适用于**活动驱动**的异质模型，不能把 V16 外生时间恢复模型的指数核移入证明。

### 严重度表的界验证

对任意 δ>0，选择 `q=e^(−2δ−5)<0.01`。九目标的损失大于 `2δ+5−ln4`，补偿资产损失大于 `−ln4`；因此第九大损失与平均损失均严格大于 δ。表中的 `M=10^20, max H_i^-<3×10^24` 是构造 II **替代解析见证**的统一资源界，不是浮点算例 M=10000 的认证。

## 2. 逐项进度与严格状态

更新后的 43 项矩阵仍保留全部 ID（没有删除）：

- `drafted`: 32（已有可供下一轮全文审核的实质写作内容；不表示 32 条定理已正式证明）。
- `partial`: 4（P10、R01、A03、A07；包括确实已证的必要部分和明确剩余证明）。
- `partial_open`: 7（T03、P02、T04、T05、R02、R03、A04 等全局/尖锐性问题）。
- `not_yet_drafted`: 0。

尚未取得的是 **Gate 3 逐定理审稿后的完整证明责任及全部研究问题的实质验收**。开放的相图、中等 K、十资产滚动下限最优个数、均匀 p<1 根延拓等不能写成已证定理。

## 3. 独立检查和可复核步骤

1. `python research/v20-gate3/check_gate3_draft.py`：43 项 ID、源码/图表路径与证据标识检查；**仅结构检查**。
2. `python research/v20-gate3/audit_new_math.py`：使用标准库 `fractions.Fraction` 核对异质两笔往返的 z² 系数、解析严重度表的严格有理数充分界、`ν>1` 的资源可积表达式；**不是自动定理证明**。
3. `pdflatex` 连续三轮：本地 24 页文章模式预览无未解析交叉引用和未定义控制序列；有一处无害的 underfull hbox。该本地容器缺少 `bibtex`，沿用旧预览九条的 `main.bbl` 仅用于渲染；GitHub V16 的 33 条 BibTeX 条目没有删除，SIAM 正式构建仍需在完整环境中验证。
4. 本地 `main.pdf` 已按页检查关键数学表格、标题、长公式、文献。6 张 PDF 图继续引用 V19 原图，其中 I/II 图保持 `NUMERIC_ONLY`，III 为内部双实现区间证据，不称外部形式认证。

## 4. 论文目前与下一阶段之间的界限

- 这是一版 **Gate 3 work-in-progress**，不能作为独立英文投稿定稿。
- `P12` 的新异质加权公式和局部反例是独立解析推进，但无法代替未完成的全局 `(p,K,N,graph)` phase diagram。
- 原始 40 页稿和 V16 用于逐研究问题和技术证明覆盖度对照，不要求机械地凑满 40 页；本轮正文与附录 24 页，下一步应审核正文主结果是否自足、附录参数计算与参考文献质量、未决开放问题的实质论证。
- Gate 4 的逐公式中文翻译和双语可批注 Word 仍未开始，须先冻结英文数学内容。