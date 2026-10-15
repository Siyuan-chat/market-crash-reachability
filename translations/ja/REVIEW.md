# 日本語訳の確認記録

基準：英語コミット `e5339a47f29ccb669d1f228ca930a1c1146200bf`、2026-10-15。英語原稿が数学上の権威である。著者による訳文の審査・承認は未完了。

## 翻訳範囲

主文と全付録、補足資料の全節・説明・図表題・表内説明を訳した。主文の仮定1件、定義2件、定理9件、命題8件、証明16件、図6件、表3件、および補足の図18件・表1件の構造を維持した。本文を要約で置き換えた箇所はない。

## 実施した検査

共有検査器 `scripts/check_translation_consistency.py` を実行した。結果は `build/translations/consistency.json`。

| 検査 | 主文 | 補足 |
|---|---|---|
| 保護された数学単位 | 926 / 926 一致 | 90 / 90 一致 |
| 数学単位の順序・内容差異 | 0 | 0 |
| label / ref / eqref / cite の順序 | 一致 | 一致 |
| 定理環境の順序 | 一致 | 一致 |
| 図ファイル列・表数・表セル区切り数 | 一致 | 一致 |
| 数式外の原文数値列 | ASCII境界の修正後に一致 | ASCII境界の修正後に一致 |
| 未翻訳の英語散文行 | 0 | 0 |

上記は構造保全の検査であり、翻訳の学術的妥当性や定理の真偽を機械的に保証するものではない。初回検査では、数式トークンの順序が一致していても数量と時刻の説明が逆になる誤訳を見落とした。以下の再点検で修正した。構造検査のPASSを意味の正確性の保証と解釈してはならない。

英語の数詞は文脈に応じた日本語表記とする。正式識別子である `M2`、`M3`、`M4`、および `MSC 2020: 91G15, 91G45, 93B03, 65G30, 91G80` は原文の算用数字・英字表記を維持する。検査器のためにこれらを漢数字化しない。原文の “one-form” は「微分一形式」と訳し、英語の数詞 one と日本語の「一」の意味対応を保つ。原文に明示された算用数字・小数・百分率および数式内の数字は維持する。表題前のメタデータでは月を日本語化し、基準版・日付と未審査状態を記す短い訳文声明を追加した。

## 数式と散文の意味対応の再点検

主文の全節・全証明・付録と、補足資料の全文を再読し、数量、取引時刻、資産添字、価格、条件、極限、終端状態の対応を確認した。今回の主な修正は次の通り。

- 主文の「株数中立取引との比較」（英語原文172行、日本語176行）：十分小さい `a>0` は購入株数、`0` は購入時刻、`a` は売却株数、`T` は売却時刻である。数量と時刻を取り違えていた日本語を修正した。数式そのものと順序は維持した。
- 仮定参照の `M2`、`M3`、`M4` とMSC分類コードを原文どおり復元した。
- カット容量命題では、`i∈J` は資産添字であり、その資産の「価格」が基準以下にあることを明記した。価格を掛けた執行容量が売買代金の受入容量であることも明確にした。
- 認証構成の `0.97` と `0.9409` は、同じ九資産の第一・第二セッションの終値であることを明記した。補足の二段階価格経路も各セッションへの対応を明示した。
- インパルス量と執行時刻の「それぞれ」の対応を明確にし、順序統計量の定義の挿入句と微分一形式の完全微分性の表現を整えた。

修正後、検査器の抽出関数を読み取り利用して再照合した。主文926単位、補足90単位の数学は、原文と文字列・順序が完全一致する。参照・引用列と定理環境列も一致し、未翻訳英語散文行は両方0である。数式外数値の旧境界判定では主文が一致、補足が不一致となった。補足には原文どおりの「第1日」「第2日」「セッション1」「セッション2」が存在するが、旧判定の `\w` は日本語も単語文字とみなすため、自然な日本語に隣接する数字を検出しない。主担当が数字境界をASCIIの英数字に限定するよう検査器を修正した。正式識別子と自然な日本語隣接数字はそのまま維持し、英語数詞 one に対応する「微分一形式」の表記を用いた。修正後の数値列は主文・補足とも一致する。

この再点検では、上記修正後に未修正の数学量の役割取り違えは新たに見つからなかった。ただし、独立した日本語専門査読・著者審査を実施したという意味ではない。

## 用語

- response-adapted generalized price coordinate：応答適合型一般化価格座標
- price impact：価格インパクト
- recovery dynamics：価格の回復ダイナミクス
- systemic drawdown：システミック・ドローダウン
- reachability：到達可能性
- paired-dollar settlement：売買代金のペア決済
- zero terminal executed-dollar ledger：終端累積売買代金フローのゼロ条件
- gross executed-share rate：総売買執行速度

文脈に応じて「ペア売買代金」「終端売買代金ゼロ条件」等の短縮形も用いた。share-flat は「株数中立」、dollar-flat は「売買代金中立」と区別する。lower-limit close は「下限終値」であり、未約定売り注文のある「ストップ安張り付き」と区別する。

## 意図的に残した英語

数学保全を優先し、次の数学内テキストは原文のままとした。場所は `main.tex` 内の安定した式ラベルで示す。

- `eq:minbudget`：`\text{ admissible}`
- `eq:constrained-crisis`：`\hbox{for all }`
- `eq:rate-energy`：`\hbox{for every qualifying asset.}`
- `eq:local-speed-crash`：`\text{for every }`
- `eq:no-second-condition`：`\text{for every }`
- `eq:allclosed`：`\text{for every }`

数式中の `trade`、`gross`、`floor`、`end` 等の添字・演算表記も原文を維持した。著者名、引用キー、参考文献の原題、ソースファイルパス、プログラム名、原図PDF内のラベルは原資料を保持する。補足の数学内説明には上記のような英語散文残留はない。

## 残る確認

LuaLaTeXによる実ビルド、文献処理、改ページ、禁則・長文の折り返し、図表の視覚確認、コンパイル後の参照番号照合は主担当の統合検証事項である。本担当は実施していない。著者には専門用語、危機とドローダウンの使い分け、対数損失と単純価格損失、必要条件と十分条件、計算機支援認証と高精度数値診断の区別を最終確認していただく必要がある。公開権限と翻訳著作権の承認も未取得である。


## Integration review — 2026-10-15

LuaLaTeX-ja preambles omit microtype for compatibility. Chinese serif, bold, italic and sans serif families are explicitly Fandol; Japanese uses HaranoAji. No font binaries are distributed. An invalid spaced table dimension in the Japanese supplement was restored to the canonical `.48\linewidth`. The Japanese Appendix wording at the two-pulse expansion was corrected to distinguish the k-th largest loss from the small amplitude h; formula content and order are unchanged. All four PDFs compile without missing glyph or overfull warnings; compiled label numbers and exact mathematical units match English. Author language acceptance remains pending.
