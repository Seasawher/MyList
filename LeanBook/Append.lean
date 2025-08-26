import LeanBook.MyList --#
/- # Appendの結合性 -/

namespace MyList

variable {α : Type}

protected def append (l₁ l₂ : MyList α) : MyList α :=
  match l₁ with
  | ⟦⟧ => l₂
  | head :: tail => head :: (MyList.append tail l₂)

/-- `MyList.append`を`++`で書けるようにする -/
instance : Append (MyList α) where
  append := MyList.append

@[simp, grind _=_]
theorem cons_append (head : α) (tail l : MyList α) :
    (head :: tail) ++ l = head :: (tail ++ l) := by
  rfl

theorem append_cons (head : α) (tail l : MyList α) :
    l ++ head :: tail = l ++ (⟦head⟧ ++ tail) := by
  rfl

@[simp, grind]
theorem nil_append (l : MyList α) : ⟦⟧ ++ l = l := by
  rfl

@[simp, grind]
theorem append_nil (l : MyList α) : l ++ ⟦⟧ = l := by
  induction l with grind

@[grind _=_]
theorem append_assoc (l₁ l₂ l₃ : MyList α) :
    (l₁ ++ l₂) ++ l₃ = l₁ ++ (l₂ ++ l₃) := by
  induction l₁ with grind

end MyList
