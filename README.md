Subspがメインのフォルダで、
SubspRepoが作業フォルダです。

## stopのファイル構成

`stop` 関連の証明は、役割ごとに次の6ファイルへまとめています。
公開定理は従来どおり `import Subsp.new.stop` で利用できます。

| ファイル | 役割 |
| --- | --- |
| [stop_algebra.lean](Subsp/new/stop_algebra.lean) | collapse・cardinal演算・翻訳ベクトルの基礎補題 |
| [stop_nf_order.lean](Subsp/new/stop_nf_order.lean) | 正規形の保存、順序埋め込み、翻訳の上界、NFの整列性 |
| [stop_ot.lean](Subsp/new/stop_ot.lean) | OTの基底、共終性、下方閉性、正規形による特徴付け |
| [stop_inverse.lean](Subsp/new/stop_inverse.lean) | 深さ・台の上界を保つcollapseとcardinal演算の逆構成 |
| [stop_surjectivity.lean](Subsp/new/stop_surjectivity.lean) | SubNFへの翻訳と全次元での全射性 |
| [stop.lean](Subsp/new/stop.lean) | OTとSubNFの順序同型、公開定理の入口 |

公理依存の検査は `lake env lean SubspRepo/StopAxiomAudit.lean` で実行できます。

## 証明方針

タクティクは、次の条件を満たす場合に使用できます。

- 使用前より証明が短くなること。
- `#print axioms` で、証明結果が `Classical.choice` に依存しないことを確認すること。

### 検証

タクティクの変更後はLeanでビルドし、変更した定理と主要な公開定理について
`#print axioms` を実行します。`Classical.choice` が含まれる変更は採用しません。
既存の主要定理の公理依存は `propext` と `Quot.sound` のみです。

`sorry`・`admit` などの未証明部分や、証明を置き換える公理の追加は認めません。
mathlibには依存しません。
