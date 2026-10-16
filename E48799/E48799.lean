import JudgeProblem

def submission : Goal := by

  let A : Sum Nat Nat → Sum Nat Nat
    | Sum.inl n => Sum.inl (Nat.succ n)
    | Sum.inr 0 => Sum.inl (Nat.succ 0)
    | Sum.inr (Nat.succ _) => Sum.inl 0

  let B : Sum Nat Nat → Sum Nat Nat
    | Sum.inl 0 => Sum.inr 0
    | Sum.inl (Nat.succ n) => Sum.inl n
    | Sum.inr n => Sum.inr (Nat.succ n)

  let C : Sum Nat Nat → Sum Nat Nat
    | Sum.inl n => Sum.inl (Nat.succ n)
    | Sum.inr 0 => Sum.inl 0
    | Sum.inr (Nat.succ n) => Sum.inr n

  let op : Sum Nat Nat → Sum Nat Nat → Sum Nat Nat
    | x, Sum.inl 0 => B x
    | x, Sum.inl (Nat.succ _) => x
    | x, Sum.inr 0 => C x
    | x, Sum.inr (Nat.succ _) => A x

  let m : Magma (Sum Nat Nat) := { op := op }
  refine ⟨Sum Nat Nat, m, ?_⟩

  have hCB : ∀ p : Sum Nat Nat, C (B p) = p := by
    intro p
    cases p with
    | inl n =>
        exact
          Nat.rec
            (motive :=
              fun n : Nat =>
                C (B (Sum.inl n : Sum Nat Nat))
                  = (Sum.inl n : Sum Nat Nat))
            (by rfl)
            (fun n _ => by rfl)
            n
    | inr n =>
        rfl

  have hBC : ∀ p : Sum Nat Nat, B (C p) = p := by
    intro p
    cases p with
    | inl n =>
        rfl
    | inr n =>
        exact
          Nat.rec
            (motive :=
              fun n : Nat =>
                B (C (Sum.inr n : Sum Nat Nat))
                  = (Sum.inr n : Sum Nat Nat))
            (by rfl)
            (fun n _ => by rfl)
            n

  have hBAA : ∀ p : Sum Nat Nat, B (A (A p)) = A p := by
    intro p
    cases p with
    | inl n =>
        rfl
    | inr n =>
        exact
          Nat.rec
            (motive :=
              fun n : Nat =>
                B (A (A (Sum.inr n : Sum Nat Nat)))
                  = A (Sum.inr n : Sum Nat Nat))
            (by rfl)
            (fun n _ => by rfl)
            n

  constructor

  · intro x y
    change op x y = op (op (op x y) y) (op y y)

    cases y with
    | inl yn =>
        exact
          Nat.rec
            (motive :=
              fun yn : Nat =>
                op x (Sum.inl yn)
                  =
                op
                  (op (op x (Sum.inl yn)) (Sum.inl yn))
                  (op (Sum.inl yn) (Sum.inl yn)))
            (by
              change B x = C (B (B x))
              exact (hCB (B x)).symm)
            (fun yn _ => by
              rfl)
            yn

    | inr yn =>
        exact
          Nat.rec
            (motive :=
              fun yn : Nat =>
                op x (Sum.inr yn)
                  =
                op
                  (op (op x (Sum.inr yn)) (Sum.inr yn))
                  (op (Sum.inr yn) (Sum.inr yn)))
            (by
              change C x = B (C (C x))
              exact (hBC (C x)).symm)
            (fun yn _ => by
              change A x = B (A (A x))
              exact (hBAA x).symm)
            yn

  · intro hg

    have hw :=
      hg
        (Sum.inr (Nat.succ 0) : Sum Nat Nat)
        (Sum.inr (Nat.succ 0) : Sum Nat Nat)

    change
      (Sum.inl 0 : Sum Nat Nat)
        =
      (Sum.inl (Nat.succ 0) : Sum Nat Nat)
      at hw

    have hw2 :=
      congrArg
        (fun s : Sum Nat Nat =>
          match s with
          | Sum.inl 0 => false
          | Sum.inl (Nat.succ _) => true
          | Sum.inr _ => true)
        hw

    change false = true at hw2
    exact Bool.false_ne_true hw2
