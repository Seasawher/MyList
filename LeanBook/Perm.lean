import LeanBook.Append --#
/- # 置換関係 -/
/--
二つのリストが「置換関係」にあるとは、同じ要素を同じ回数だけ含んでいる（順序は一致しなくてもよい）ことをいう。

一方のリストから他方のリストへ、隣接する要素の交換を繰り返すことで変換できることを示せば、
その二つは置換関係にあると証明できる。
-/
@[grind]
inductive MyPerm {α : Type} : MyList α → MyList α → Prop
  /-- 空リストは空リストの置換である `[] ~ []`. -/
  | nil : MyPerm ⟦⟧ ⟦⟧
  /--
  一方のリストが他方の置換であるとき、両方の先頭に同じ要素を付けても置換関係は保たれる：
  `l₁ ~ l₂ → x :: l₁ ~ x :: l₂`。
  -/
  | cons (x : α) {l₁ l₂ : MyList α} : MyPerm l₁ l₂ → MyPerm (x :: l₁) (x :: l₂)
  /--
  先頭二要素を入れ替えただけのリスト同士は置換関係にある：`x :: y :: l ~ y :: x :: l`。
  -/
  | swap (x y : α) (l : MyList α) : MyPerm (y :: x :: l) (x :: y :: l)
  /--
  置換関係は推移的である：`l₁ ~ l₂ → l₂ ~ l₃ → l₁ ~ l₃`。
  -/
  | trans {l₁ l₂ l₃ : MyList α} : MyPerm l₁ l₂ → MyPerm l₂ l₃ → MyPerm l₁ l₃

/-- 置換関係`MyPerm`を表す記号。標準ライブラリでは記号`∼`を使用するが、被らないようにしている。 -/
infixl:50 " ≈ " => MyPerm

/- ## 推移的であること -/

instance {α : Type} : Trans (· ≈ · : MyList α → MyList α → Prop) (· ≈ ·) (· ≈ ·) where
  trans := MyPerm.trans

/- ## 証明の例 -/

example : ⟦1, 2⟧ ≈ ⟦2, 1⟧ := by grind

example : ⟦1, 2, 3⟧ ≈ ⟦3, 2, 1⟧ := calc
  _ ≈ ⟦2, 1, 3⟧ := by grind
  _ ≈ ⟦2, 3, 1⟧ := by grind
  _ ≈ ⟦3, 2, 1⟧ := by grind
