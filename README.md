## 証明方針

タクティクは、次の条件を満たす場合に使用できます。

- 使用前より証明が短くなること。
- `#print axioms` で、証明結果が `Classical.choice` に依存しないことを確認すること。

### 検証

タクティクの変更後はLeanでビルドし、変更した定理と主要な公開定理について
`#print axioms` を実行します。`Classical.choice` が含まれる変更は採用しません。
既存の主要定理の公理依存は `propext` と `Quot.sound` のみです。

`ProofAudit.lean` はプロジェクト内の全定義・定理（自動生成された証明を含む）に
`#print axioms` を実行し、`propext`・`Quot.sound` 以外の公理依存があれば失敗します。

```sh
lake build Subsp Subsp.new.stop
lake env lean ProofAudit.lean
```

`sorry`・`admit` などの未証明部分や、証明を置き換える公理の追加は認めません。
mathlibには依存しません。
