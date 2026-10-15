# 中文译稿审校记录

译稿日期：2026-10-15。英文权威基线：V12 Final。

## 覆盖与方法

- 主文完整覆盖原始 988 行结构，包括全部正文、证明、附录、图表题与声明；补充完整覆盖原始 121 行结构，包括全部探索性说明、表格及诊断图题。未以摘要、占位符或删节替代正文。
- 行内数学由原文逐行抽取，中文中以索引定位后原样回填；写入时断言每个原文片段恰使用一次。初版曾按中文语序调整少量同句公式顺序；严格检查发现不符合顺序要求后，已逐句修复，最终数学单元顺序与英文完全一致。
- 所有展示数学块直接保留，未改公式中的英语。`label`、`ref`、`eqref`、`citep`、`citet` 命令及参数保留。定理共享计数器定义、公式编号规则与英文相同，只译环境显示名。
- 统一术语：response-adapted generalized coordinate 为“响应适配广义价格坐标”；response-adapted coordinate 为“响应适配坐标”；resilience 为“韧性”；paired-dollar execution 为“成交金额配对执行”；gross executed-share rate 为“毛成交股数速率”；terminal dollar closure 为“终点净成交金额闭合”；gross execution rate 为“毛成交速率”；breadth 为“覆盖广度”；compensator 为“补偿资产”；witness 为“见证”。

## 实际完成的静态检查

以 Python 对最终翻译文本与英文源文件进行比较：初步检查确认主文 95 个展示数学块逐字一致，补充 2 个展示数学块逐字一致；两文件行内数学多重集合一致。该初步检查不足以验证顺序，随后按共享检查器执行了下述严格顺序检查。主文 `label` 137 项、`ref` 34 项、`eqref` 62 项、`citep` 27 项均与原文多重集合一致；补充 `label` 21 项一致，未新增交叉引用。英文连续短语扫描未发现遗漏的独立正文段落。

未运行编译、BibTeX、字体探测或 PDF 渲染；未声称已经通过作者语言验收。最终构建与独立数学复核由主 agent 执行。中文长图题和表格可能需要最终版式检查。

## 保留的英文与待审事项

为严格保留数学环境，下列公式内文字保留英文（位置按英文源文件行号及稳定公式标签给出；中文稿若增加译本声明，行号会偏移）：

| 英文源位置 | 标签 | 保留文字 |
|---|---|---|
| `paper/main.tex:155` | `eq:minbudget` | `\text{ admissible}` |
| `paper/main.tex:376` | `eq:constrained-crisis` | `\hbox{for all }` |
| `paper/main.tex:405` | `eq:rate-energy` | `\hbox{for every qualifying asset.}` |
| `paper/main.tex:444` | `eq:local-speed-crash` | `\text{for every }` |
| `paper/main.tex:580` | `eq:no-second-condition` | `\text{for every }` |
| `paper/main.tex:880` | `eq:allclosed` | `\text{for every }` |

另保留作者及被引作者姓名、数学符号及数学缩写、MSC 分类码、TSE/OHLCV/AI 等缩写、程序与文件路径、软件名称、原文参考文献题名，以及原始 PDF 图内的英文标签。原图内文字未在本分配范围内重绘。补充图 `fig:streak-rate` 原文含重复的“scalar constant-impact”短语，中文以完整语义表述保留其比较模型限定，不重复制版错误。

作者需审阅经济与数学术语、个别长句对应关系及中文文风；图形内嵌英语若要求全中文视觉版，需在另行明确的图形编辑范围内处理。不存在新增的统计结论、实证校准或作者批准公开声明（此处为初次审校记录；现已另获作者公开授权）。

## 严格顺序复核（修订后）

实际运行 `scripts/check_translation_consistency.py`，以本文件为临时指定报告目标读取原始 JSON 后恢复为本审校记录；未修改共享检查器，也未改变其断言或放宽条件。未写入其他报告或共享文件。

- `main.tex`：**PASS**；数学单元 926/926，顺序或内容差异 0；引用及标签顺序一致：True；定理环境顺序、图形、表数量、表单元分隔符及正文数字序列均一致；遗漏英文正文段落 0。
- `supplementary.tex`：**PASS**；数学单元 90/90，顺序或内容差异 0；引用及标签顺序一致：True；定理环境顺序、图形、表数量、表单元分隔符及正文数字序列均一致；遗漏英文正文段落 0。

检查器本次整体退出码为 0；日文译本仍由其他工作负责，不将其状态计入中文验收。中文语言质量仍待作者验收，且本次未运行编译和视觉检查。


## Integration review — 2026-10-15

LuaLaTeX-ja preambles omit microtype for compatibility. Chinese serif, bold, italic and sans serif families are explicitly Fandol; Japanese uses HaranoAji. No font binaries are distributed. An invalid spaced table dimension in the Japanese supplement was restored to the canonical `.48\linewidth`. The Japanese Appendix wording at the two-pulse expansion was corrected to distinguish the k-th largest loss from the small amplitude h; formula content and order are unchanged. All four PDFs compile without missing glyph or overfull warnings; compiled label numbers and exact mathematical units match English. Public distribution has been authorized by the author; further language review remains possible.

## 全文证明与语义角色深审（2026-10-15）

重新通读中文主文全部正文、定理/命题及证明、附录和完整补充材料，结合英文源文核对公式周围的语义角色，重点检查股数与时刻、顺序统计量与小参数、初终值、正负号、必要/充分条件、量词以及认证范围。共享检查器的数学 token 顺序通过不能替代这类检查。

本轮修正：

- `main.tex:264`、`:443`：改顺局部光滑性条件的中文表述，保持函数、光滑性阶数、适用邻域三个数学角色及原顺序不变。
- `main.tex:392`：将“每个成交金额配对”澄清为配对交易金额在买卖两侧的重复核算，解释因子二的来源。
- `main.tex:621`：将含混的“该积分”明确为包含恢复速率系数的恢复积分，避免误读为左侧坐标微分的积分。
- `main.tex:740`：删除术语替换产生的重复“成交”。
- `main.tex:798`：将 compact neighborhood 的“紧邻域”修正为“紧致邻域”，保留紧致性这一技术限定。
- `main.tex:822`：将可能限于三维的“正卦限”改为“严格正坐标区域”，适用于任意资产维数。
- `main.tex:602`、`:778`、`:800`：改顺终止状态与展开中心的表述；未调换数学单元。
- 补充表格将“最大总股数卖出”改为“最大累计卖出股数”，明确其为累计量而非瞬时速率。

明确复核但无需改动：`main.tex:173` 正确对应“买入小股数 a 于时刻零、卖出相同股数于终点”；`:805` 正确对应“第 k 大损失在小参数 h 充分小时为正”。五条市场假设的 M1--M5 编号模板及正文 M2/M3/M4 等引用按英文原样保留，未译为中文数字或改变编号。

修正后再次实际运行未修改的共享检查器（临时输出仍限于本文件，读取 JSON 后恢复 Markdown）：
- 中文 `main.tex`：PASS，数学单元 926/926，差异 0；引用标签顺序、正式环境顺序、图表与数字序列均通过。
- 中文 `supplementary.tex`：PASS，数学单元 90/90，差异 0；引用标签顺序、正式环境顺序、图表与数字序列均通过。

本轮未发现股数/时刻或顺序统计量/小参数互换的新错误；并不据此宣称译文绝无遗漏。局限：这是译文与原文的语义一致性审校，不是数学定理的独立重证、数值证书的重新运行或 PDF 版式检查；作者语言验收仍待完成。
