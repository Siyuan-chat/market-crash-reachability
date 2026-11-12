# Gate 4 — 双语论文交付与可审计文档审查

**审查日期：2026-11-12；状态：GATE 4 IN PROGRESS / DOCUMENT AUDIT PASSED WITH VISUAL-RENDERING EXCEPTIONS。**

此审计仅针对 Handoff 中的 Gate 4 翻译与可编辑 Word，不重新研究 Gate 0–3，也不提升 Gate 3 scoped scientific acceptance 的主张强度。

## 冻结基准与资产核验

- 原 Handoff ZIP 中的 `03_VERIFY_HANDOFF.py` 成功运行，25/25 文件 SHA-256 一致，ZIP 完整；这 25 个指 manifest 路径文件。
- 唯一英文正文真值为 `submission/v20-gate3-activity-recovery/main.tex`；SHA-256：`9d36ab61019bcb395073918c133bfc4a4cf23c32b99efd9a84c021fb7d092baa`。
- 原始参考文献 `references.bib` SHA-256：`555df0a2e0bb6a3749cf64a144626b8f3d086c3a5d95e97ce5d31551701de0f2`；33 条 BibTeX，实际正文引用 16 条。
- 正式 SIAM 35 页 `main.pdf` SHA-256：`25c0f8977bf45936420398acfed33a85657314d0fa03c004ca84b00f723b9e0b`；编号以真实 `main.aux` 为准。
- GitHub `main` 在本次审查时核实为 `8a2dacea4e65ed052820b7ab4d8a1f827c058ccb`。不触碰 V16/V17 版本、原 PDF、发布和 DOI。

## 英文 Word 与中文 Word 对照审查

- 英文原稿 386 个 Word 段落（含表中段落），审阅副本为 387（新增正式参考文献标题）。中英文布局各有 387 个对应段落。
- 翻译了 **259 个含英语自然语言的正文/标题/证明/附录段落**，包括 A–E 技术附录；公式段保留英文冻结源的数学字符；参考文献保留正式书目外文姓名与出版数据。
- 每份 Word 均含 **1326 个原生 `m:oMath` 节点、106 个 `m:oMathPara` 展示数学段、6 张真实研究图和 2 张表**。
- 数学对象在**未经字体兼容补丁**的中英文 SIAM-aligned Word 中与原英文 Word 的数学 XML 多重集合一致，逐段 0–369 数学 XML 多重集合一致；图像媒体摘要一致。
- 为改善 LibreOffice 导入异常，ReviewReady 版只增加部分 OMML 数学 run 的 `m:nor` 字形属性（300 个脚标单符号、102 个标点、17 个行首关系符号、29 个星号及 11 个 sup 算子），未改变所有 `m:t` 字符、数学算子标签或数学对象个数。已使用忽略运行时字形样式的规范化 OMML 树做**逐数学对象**全量等同性检查：通过。
- 参考文献正文交叉引用和文末实际排序修正为 SIAM `main.bbl` 16 条的作者排序；留存旧→新编号及 BibTeX key 全表。
- 数学主结果：12 个 theorem、14 个 proposition、5 个 lemma、2 个 corollary，合计 33；对应标题与编号在中英文 Word 均已定位。
- 从 `main.aux` 中去掉 `@cref` 二级别名后，**131/131 个主标签找到中英文段落锚点**，涵盖 65 `eq`、15 `sec`、14 `prop`、12 `thm`、8 `app`、6 `fig`、5 `lem`、2 `def`、2 `cor`、2 `tab`。跨文字编号、公式和图表的核对结果见 CSV。
- 所有 43/43 项科学写作责任均原封不动复制入审计登记文件。仍含未解决数学子问题的原始 ID：`T03`, `P02`, `P10`, `R01`, `R02`, `R03`, `A04`；数学研究未宣称 43/43 问题求解。

## 逐页 PDF 渲染及兼容性问题

- 审阅稿用同一个 LibreOffice 环境从 DOCX 独立渲染：**英文 31 页、中文 30 页**。该页数允许不同于 35 页的 SIAM 正式 PDF。
- 每份已检查每一页都有实质正文（英文最少 813 个提取字符，中文最少 182 个），文本块均在页面范围内，无检出的空白页/页面越界。已检查两份共 61 页的 contact sheet。
- **尚有排版兼容性例外：**LibreOffice 从复杂原生 OMML 导入会产生红色错误字形 `¿`，修补前中英文各 **162** 处，修补后各 **14** 处。此数值是渲染器替代字形的检测计数，**不能据此断定 Word 数学公式内容失真或判定 Microsoft Word 相同显示**；但也**不应将这两个 Word 的全页视觉审查表述为完全通过**。相关位置可用渲染文件及逐页 JSON 追踪。
- 因存在上述 14 处 LO 渲染问题，Gate 4 全面交付验收 **NOT CLEARED**；后续应使用 Microsoft Word 原生渲染确认或继续逐处消除兼容性错误，并对翻译作独立逐句语义校对。

## 科学断言范围及翻译红线

- 不把 `C_α` 的终端共同损失写成危机概率、首次穿越概率或滚动峰值回撤；保留每资产 `X_i(T)=0`、卖方实际股份库存 `H_i^-`，区分 `C0/C1`。
- 核心构造 I 为十资产精确半价解析高预算正平滑见证；II 为每个固定 `0≤p<1` 的九资产任意严重度与有限共同预算包络；III 为同五资产连续两日 ±25% 下限的内部区间验证 C1 证书，非外部形式认证。
- 旧低预算数值轨迹继续为 `NUMERIC_ONLY`，未提升为解析定理；`5≤k*≤9`、全资产 sharp 损失界、最优最小速率仍 OPEN。

## 文件哈希清单

| 交付件 | SHA-256 |
|---|---|
| English ReviewReady Word (`Gate4_When_Can_Markets_Crash_English_Full_Editable_ReviewReady_v20.docx`) | `c332d81b872e537dcbe50b81fd770f37c1c43a37be8efbeea931fb36c3c59a68` |
| Chinese ReviewReady Word (`Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_ReviewReady_v20.docx`) | `da4e094ddf0503512bac352e2719f349011ac27ade25565482d3be89997a1071` |
| English unpatched exact-OMML Word (`Gate4_When_Can_Markets_Crash_English_Full_Editable_SIAM_Aligned_v20.docx`) | `6be34d9a059d0e7a07edca8b096bfbface21302b328cdc6342ce6580b31ad8cf` |
| Chinese unpatched exact-OMML Word (`Gate4_When_Can_Markets_Crash_Chinese_Full_Editable_SIAM_Aligned_v20.docx`) | `c274c2ec3b30a0aa2a8b8c85f9125894f8843f3e994331cb6a7aed68440d1a28` |
| English Markdown review source (`Gate4_When_Can_Markets_Crash_English_Full_Source_SIAM_Aligned_v20.md`) | `7c2ad644aaa9339fab582cf7bcfff2cb72814cb0ab6e30825656e208d3990c16` |
| Chinese Markdown review source (`Gate4_When_Can_Markets_Crash_Chinese_Full_Source_SIAM_Aligned_v20.md`) | `274e35b49a5637502918a7bb6f8012ea7fa63aa400f11e789267d34635b9bc5c` |
| SIAM frozen original PDF 35p (`main.pdf`) | `25c0f8977bf45936420398acfed33a85657314d0fa03c004ca84b00f723b9e0b` |

## 可复算审查记录

- `GATE4_131_LABEL_WORD_CROSSWALK.csv`：131 条 source label→ SIAM PDF 页码和编号 → EN/ZH Word 段落位置；全文数学节点并非 131 个。
- `GATE4_43_RESPONSIBILITIES_UNCHANGED.csv`：原 43 项追踪登记原值复制；不重新标记结案。
- `GATE4_SIAM_REFERENCE_RENUMBERING.csv`：16 项 BibTeX key、旧 Word 引文序号及 SIAM 正式序号。
- `GATE4_DOCUMENT_AUDIT.json`：冻结 SHA、公式 XML、图表、标签与初版页面渲染检查。
- `GATE4_REVIEWREADY_RENDER_QA.json`：ReviewReady 数学结构等同性、页面与 14 处剩余 glyph 的逐页计数。
- `verify_gate4_docs.py`、`verify_reviewready_omml.py`、`fix_omml_render_style.py`：可复验脚本。

## GitHub、交付和验收结论

本次进展可以作为**审计阶段的 PR**提交并经验证后合并，但最终中文/英文 Word 的二进制本体通过对话附件交付；如仓库接口只支持文本写入，则不得宣称 DOCX 已上传 GitHub。PDF 的真实构建保留为既有冻结的 35 页 SIAM 工件。

**Gate 4 现状：双语内容生成及结构交叉验收完成；可编辑 Word 可供人工批注；LibreOffice 仍有已量化的数学渲染兼容例外；后续尚需 Word 原生渲染及独立语义校核才能全面 CLEAR。**