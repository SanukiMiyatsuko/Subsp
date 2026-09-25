Subspがメインのフォルダで、
SubspRepoが作業フォルダです。

## 証明方針

このリポジトリでは、証明の構成性と明示性を保つため、使用するタクティクを制限します。

### 許可する公理

使用を許可する公理は次の2つだけです。

- `propext`
- `Quot.sound`

`Classical.choice` など、これ以外の公理への依存は認めません。

また、mathlib には依存しません。

### 禁止タクティク

以下のタクティクおよびタクティクコンビネータは禁止します。

#### 自動化・探索

- `simp`
- `simpa`
- `simp_all`
- `dsimp`
- `aesop`
- `assumption`
- `trivial`
- `try`
- `repeat`
- `omega`
- `all_goals`
- `any_goals`
- `first`
- `first_goals`
- `solve`
- `solve_by_elim`
- `apply_rules`
- `grind`
- `<;>`

#### 決定手続き・自動証明

- `decide`
- `native_decide`
- `bv_decide`
- `linarith`
- `nlinarith`
- `ring`
- `ring_nf`
- `norm_num`
- `positivity`
- `tauto`

#### 自動候補生成

- `exact?`
- `apply?`
- `rw?`
- `simp?`

#### 暗黙の場合分け・パターン分解・等式処理

- `by_cases`
- `by_contra`
- `split`
- `rcases`
- `obtain`
- `injection`
- `subst`
- `conv`

### 禁止する非構成的・未証明構文

タクティクではありませんが、以下も禁止します。

- `classical`
- `Classical.em`
- `Classical.choice`
- `propDecidable`
- `noncomputable`
- `sorry`
- `admit`

### 許可タクティク

証明過程がソースコード上で明示的に追える、以下のタクティクを使用できます。

- `intro`
- `exact`
- `apply`
- `refine`
- `have`
- `show`
- `change`
- `rw`
- `rfl`
- `unfold`
- `cases`
- `induction`
- `constructor`
- `left`
- `right`
- `exfalso`
- `clear`

また、ゴールを明示的に選択するための `case` / `next` 構文も使用できます。

タクティクではありませんが、以下のような明示的な項・場合分けも使用できます。

- `match ... with`
- `exact match ... with`
- `Decidable.byCases`
- `cases (inferInstance : Decidable p)`

特に命題の真偽で場合分けする場合、`by_cases` は使用せず、利用可能な `Decidable p` を明示的に消去してください。

### 原則

「Lean が何を試したか」ではなく、「どの証明項・どの等式・どの constructor を使ったか」がコードから直接読める証明を優先します。

禁止リストにない新しいタクティクを導入する場合でも、証明探索、自動簡約、暗黙の古典論理、暗黙の witness 抽出、暗黙の等式分解を行うものは使用しないでください。
