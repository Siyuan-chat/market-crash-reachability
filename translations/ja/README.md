# 日本語学術訳

対象は `paper/main.tex` の主文全体と付録、ならびに `supplementary/supplementary.tex` の補足資料全体である。表題、要旨、キーワード、本文、仮定・定義・定理・命題、証明、図表題と表内の説明、結論、再現性・データ利用可能性、AI支援ツール声明を含む。要約版ではない。

- 原文の基準版：英語 V12 Final
- 訳文の基準日：2026-10-15
- 数学上の権威：英語 V12 Final 原稿
- 状態：全範囲の訳文草稿。著者の許可を得て公開する。今後の言語校訂は可能である。

`main.tex` と `supplementary.tex` は LuaLaTeX 用で、`fontspec`、`luatexja-fontspec` および `HaranoAjiMincho-Regular.otf` を用いる。図は原文の PDF を相対参照し、主文の参考文献は原文の `paper/references` を参照する。数式、数学環境、参照・引用キー、定理カウンタは原文を維持する。独立した番号付き「翻訳説明」節は追加しない。

統合担当がLuaLaTeXビルド、数式と参照番号の照合、PDFの視覚確認を実施した。著者による公開許可を取得済みである。実施済みの構造検査と残る確認事項は [REVIEW.md](REVIEW.md) を参照。

翻訳文に MIT ライセンスを自動適用しない。原著作物・図表・参考文献・翻訳に関する権利と公開条件は、原著作物の条件および著者の許諾に従い、著者による確認を要する。コードに適用されるライセンスだけを根拠に、論文本文・翻訳・図表への許諾を推定しない。


Canonical build from the repository root: `python scripts/build_translations.py`; then `python scripts/check_translation_consistency.py --aux-root build/translations`. PDFs: `build/translations/ja/main.pdf` and `supplementary.pdf`. Full dependency and output details: [translation build guide](../README.md).
