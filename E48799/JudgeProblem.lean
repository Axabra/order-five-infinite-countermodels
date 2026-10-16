import JudgeMagma.Magma

@[reducible] def EquationLHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x ◇ y = ((x ◇ y) ◇ y) ◇ (y ◇ y)

@[reducible] def EquationRHS (G : Type _) [Magma G] : Prop :=
  ∀ (x y : G), x ◇ y = ((x ◇ y) ◇ (y ◇ y)) ◇ y

abbrev Goal : Prop :=
  ∃ (G : Type) (_ : Magma G), EquationLHS G ∧ ¬ EquationRHS G
