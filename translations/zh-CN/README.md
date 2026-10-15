# 简体中文学术译本

本目录包含完整主文 `main.tex` 与完整补充材料 `supplementary.tex` 的简体中文译稿。范围包括标题、摘要、正文、定理与命题、证明、全部附录、图表题、表头和表内文字、代码与数据可用性以及 AI 辅助工具声明。参考文献作者、书目原题及文内引文键保留英文原貌。

英文权威基线：V12 Final，源文件为 `paper/main.tex` 与 `supplementary/supplementary.tex`。译稿日期：2026-10-15。英文原稿是数学内容的权威版本；本译本完整覆盖原文，已获作者公开授权；后续仍可进行语言校订。

## 构建

从本目录运行 LuaLaTeX；所需宏包包括 `fontspec`、`luatexja-fontspec` 及英文原文使用的数学、图形和参考文献宏包。当前字体配置为 `FandolSong-Regular.otf`。主文图形链接到 `../../paper/figures/`，补充图形链接到 `../../supplementary/figures/`，主文参考文献库链接到 `../../paper/references.bib`。

```text
lualatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
lualatex -interaction=nonstopmode -halt-on-error main.tex
lualatex -interaction=nonstopmode -halt-on-error main.tex
lualatex -interaction=nonstopmode -halt-on-error supplementary.tex
lualatex -interaction=nonstopmode -halt-on-error supplementary.tex
```

也可由负责最终构建者将英文参考文献生成文件复制为本目录的 `main.bbl`，再运行两次 LuaLaTeX。统一构建与一致性核对已由主 agent 实际执行；完整命令见上级目录 README。正文附录保留英文源文的 `pdflatex` 复现说明，并明确其适用对象为英文原文；中文译本使用本节的 LuaLaTeX 流程。

## 权利与审校

原文、译文及图形的版权和许可应分别核实。本目录没有单独授予这些论文材料 MIT 许可，仓库其他代码的许可不自动扩展到论文或译文。使用现有英文图形文件；图题已翻译，图内嵌入的英文标签及原图设计保持不变。详细残留项及实际检查见 `REVIEW.md`。

当前状态：完整译稿、LuaLaTeX 编译、数学与编号一致性及版式检查已完成；作者已授权公开，后续语言校订不改变现有版权声明。


Canonical build from the repository root: `python scripts/build_translations.py`; then `python scripts/check_translation_consistency.py --aux-root build/translations`. PDFs: `build/translations/zh-CN/main.pdf` and `supplementary.pdf`. Full dependency and output details: [translation build guide](../README.md).
