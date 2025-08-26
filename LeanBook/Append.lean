import LeanBook.MyList --#
/- # Appendの結合性 -/

variable {α : Type}

protected def MyList.append (l₁ l₂ : MyList α) : MyList α :=
  match l₁ with
  | ⟦⟧ => l₂
  | head :: tail => head :: (MyList.append tail l₂)

/-- `MyList.append`を`++`で書けるようにする -/
instance : Append (MyList α) where
  append := MyList.append

@[simp, grind _=_]
theorem MyList.cons_append (head : α) (tail l : MyList α) :
    (head :: tail) ++ l = head :: (tail ++ l) := by
  rfl

theorem MyList.append_cons (head : α) (tail l : MyList α) :
    l ++ head :: tail = l ++ (⟦head⟧ ++ tail) := by
  rfl

@[simp, grind]
theorem MyList.nil_append (l : MyList α) : ⟦⟧ ++ l = l := by
  rfl

@[simp, grind]
theorem MyList.append_nil (l : MyList α) : l ++ ⟦⟧ = l := by
  induction l with grind

-- @[grind _=_]
theorem MyList.append_assoc (l₁ l₂ l₃ : MyList α) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with grind

/- ## 結合性を再利用可能にする -/

-- 結合的であることを`ac_rfl`から再利用可能にする
instance {α : Type} : Std.Associative (α := MyList α) (· ++ ·) where
  assoc := MyList.append_assoc

example (l₁ l₂ l₃ : MyList α) : l₁ ++ (l₂ ++ l₃) = (l₁ ++ l₂) ++ l₃ := by
  ac_rfl
