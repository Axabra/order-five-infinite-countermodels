import equational_theories.Magma
import Mathlib.Tactic
namespace Eq40909ForestCompletion
def Law40909 (G : Type*) [Magma G] : Prop :=
  ∀ x y z : G, ((((y ◇ x) ◇ y) ◇ y) ◇ z) ◇ y = x
def Law28770 (G : Type*) [Magma G] : Prop :=
  ∀ x y z : G, (((y ◇ y) ◇ y) ◇ x) ◇ (y ◇ z) = x
namespace ForestARS
variable {α : Type*}
def Normal (r : α → α → Prop) (a : α) : Prop :=
  ∀ {b : α}, ¬ r a b
end ForestARS
namespace ForestTerm
inductive Term where
  | var : ℕ → Term
  | op : Term → Term → Term
deriving DecidableEq, Repr
open Term
def size : Term → ℕ
  | .var _ => 1
  | .op a b => size a + size b + 1
@[simp] theorem size_op (a b : Term) :
    size (.op a b) = size a + size b + 1 := rfl
def subst (σ : ℕ → Term) : Term → Term
  | .var n => σ n
  | .op a b => .op (subst σ a) (subst σ b)
@[simp] theorem subst_var (σ : ℕ → Term) (n : ℕ) :
    subst σ (.var n) = σ n := rfl
@[simp] theorem subst_op (σ : ℕ → Term) (a b : Term) :
    subst σ (.op a b) = .op (subst σ a) (subst σ b) := rfl
inductive Subterm : Term → Term → Prop
  | refl (t : Term) : Subterm t t
  | left {s a b : Term} : Subterm s a → Subterm s (.op a b)
  | right {s a b : Term} : Subterm s b → Subterm s (.op a b)
namespace Subterm
theorem subst_preserves
    {s t : Term}
    (h : Subterm s t)
    (σ : ℕ → Term) :
    Subterm (subst σ s) (subst σ t) := by
  induction h with
  | refl =>
      exact .refl _
  | left _ ih =>
      exact .left ih
  | right _ ih =>
      exact .right ih
theorem size_le
    {s t : Term}
    (h : Subterm s t) :
    size s ≤ size t := by
  induction h with
  | refl =>
      exact le_rfl
  | left _ ih =>
      simp only [size_op]
      omega
  | right _ ih =>
      simp only [size_op]
      omega
end Subterm
structure Node where
  A : Term
  p : Term
  q : Term
deriving Repr
def x : Term := .var 0
def y : Term := .var 1
def z0 : Term := .var 2
def A0 : Term :=
  .op (.op (.op (.op y x) y) y) z0
def node0 : Node where
  A := A0
  p := y
  q := x
def advance (n : ℕ) (N : Node) : Node where
  A := .op (.op (.op N.q N.A) N.A) (.var (n + 3))
  p := N.A
  q := N.p
def node : ℕ → Node
  | 0 => node0
  | n + 1 => advance n (node n)
def lhs (n : ℕ) : Term :=
  .op (node n).A (node n).p
def rhs (n : ℕ) : Term :=
  (node n).q
theorem p_subterm_A :
    ∀ n : ℕ, Subterm (node n).p (node n).A := by
  intro n
  induction n with
  | zero =>
      exact
        Subterm.left
          (Subterm.left
            (Subterm.left
              (Subterm.left
                (Subterm.refl y))))
  | succ n ih =>
      exact
        Subterm.left
          (Subterm.left
            (Subterm.right
              (Subterm.refl (node n).A)))
theorem q_subterm_A :
    ∀ n : ℕ, Subterm (node n).q (node n).A := by
  intro n
  induction n with
  | zero =>
      exact
        Subterm.left
          (Subterm.left
            (Subterm.left
              (Subterm.right
                (Subterm.refl x))))
  | succ n ih =>
      have hp : Subterm (node n).p (node n).A :=
        p_subterm_A n
      exact
        Subterm.left
          (Subterm.left
            (Subterm.right hp))

def RootStep (s t : Term) : Prop :=
  ∃ n : ℕ, ∃ σ : ℕ → Term,
    s = subst σ (lhs n) ∧
    t = subst σ (rhs n)
inductive Step : Term → Term → Prop
  | root {s t : Term} : RootStep s t → Step s t
  | left {a a' b : Term} : Step a a' → Step (.op a b) (.op a' b)
  | right {a b b' : Term} : Step b b' → Step (.op a b) (.op a b')
theorem var_normal (k : ℕ) :
    ForestARS.Normal Step (.var k) := by
  intro t h
  cases h with
  | root hr =>
      rcases hr with ⟨n, σ, hs, _⟩
      simp [lhs] at hs
theorem ry_ly_injective
    {G : Type*} [Magma G]
    (h : Law40909 G)
    (y z : G)
    {a b : G}
    (hab : (y ◇ a) ◇ y = (y ◇ b) ◇ y) :
    a = b := by
  calc
    a = ((((y ◇ a) ◇ y) ◇ y) ◇ z) ◇ y := (h a y z).symm
    _ = ((((y ◇ b) ◇ y) ◇ y) ◇ z) ◇ y := by rw [hab]
    _ = b := h b y z
theorem idempotent_forces_subsingleton
    {G : Type*} [Magma G]
    (h : Law40909 G)
    {y : G}
    (hyy : y ◇ y = y) :
    ∀ a b : G, a = b := by
  intro a b
  have ha : (y ◇ a) ◇ y = y := by
    simpa [hyy] using h y y a
  have hb : (y ◇ b) ◇ y = y := by
    simpa [hyy] using h y y b
  exact ry_ly_injective h y y (ha.trans hb.symm)
theorem diagonal_28770_forces_idempotent
    {G : Type*} [Magma G]
    (h : Law40909 G)
    {y : G}
    (ht :
      ((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ y)) = y) :
    y ◇ y = y := by
  have htR :
      (((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ y)) ◇ y) =
        y ◇ y :=
    congrArg (fun t : G => t ◇ y) ht
  calc
    y ◇ y =
        (((((y ◇ y) ◇ y) ◇ y) ◇ (y ◇ y)) ◇ y) := htR.symm
    _ = y := h y y (y ◇ y)
theorem not_law28770_of_nontrivial
    {G : Type*} [Magma G]
    (h40909 : Law40909 G)
    {p q : G}
    (hpq : p ≠ q) :
    ¬ Law28770 G := by
  intro h28770
  have hyy : p ◇ p = p :=
    diagonal_28770_forces_idempotent h40909 (h28770 p p p)
  exact hpq (idempotent_forces_subsingleton h40909 hyy p q)
namespace ClosedForest
noncomputable section
open ForestARS
inductive StrictSubterm : Term → Term → Prop
  | left {s a b : Term} : Subterm s a → StrictSubterm s (Term.op a b)
  | right {s a b : Term} : Subterm s b → StrictSubterm s (Term.op a b)
namespace StrictSubterm
theorem subst_preserves
    {s t : Term}
    (h : StrictSubterm s t)
    (σ : ℕ → Term) :
    StrictSubterm (subst σ s) (subst σ t) := by
  cases h with
  | left h =>
      exact .left (Subterm.subst_preserves h σ)
  | right h =>
      exact .right (Subterm.subst_preserves h σ)
theorem size_lt
    {s t : Term}
    (h : StrictSubterm s t) :
    size s < size t := by
  cases h with
  | left hsub =>
      have hs := Subterm.size_le hsub
      simp only [size_op]
      omega
  | right hsub =>
      have hs := Subterm.size_le hsub
      simp only [size_op]
      omega
theorem subst_size_lt
    {s t : Term}
    (h : StrictSubterm s t)
    (σ : ℕ → Term) :
    size (subst σ s) < size (subst σ t) :=
  size_lt (subst_preserves h σ)
end StrictSubterm
def head : ℕ → Term
  | 0 => Term.op y x
  | n + 1 => rhs n
def core (n : ℕ) : Term :=
  Term.op (Term.op (head n) (node n).p) (node n).p
theorem A_shape (n : ℕ) :
    (node n).A = Term.op (core n) (.var (n + 2)) := by
  cases n with
  | zero =>
      rfl
  | succ n =>
      rfl
theorem q_subterm_core :
    ∀ n : ℕ, Subterm (rhs n) (core n) := by
  intro n
  cases n with
  | zero =>
      change
        Subterm x
          (Term.op (Term.op (Term.op y x) y) y)
      exact
        Subterm.left
          (Subterm.left
            (Subterm.right (Subterm.refl x)))
  | succ n =>
      change
        Subterm (node n).p
          (Term.op (Term.op (rhs n) (node n).A) (node n).A)
      exact
        Subterm.right (p_subterm_A n)
theorem q_strict_A (n : ℕ) :
    StrictSubterm (rhs n) (node n).A := by
  rw [A_shape]
  exact StrictSubterm.left (q_subterm_core n)
theorem p0_strict_head0 :
    StrictSubterm (node 0).p (head 0) := by
  change StrictSubterm y (Term.op y x)
  exact StrictSubterm.left (Subterm.refl y)
theorem head_succ_strict_p (n : ℕ) :
    StrictSubterm (head (n + 1)) (node (n + 1)).p := by
  change StrictSubterm (rhs n) (node n).A
  exact q_strict_A n
theorem head_ne_p_subst
    (n : ℕ)
    (σ : ℕ → Term) :
    subst σ (head n) ≠ subst σ (node n).p := by
  cases n with
  | zero =>
      intro heq
      have hlt :=
        StrictSubterm.subst_size_lt p0_strict_head0 σ
      have hs := congrArg size heq
      omega
  | succ n =>
      intro heq
      have hlt :=
        StrictSubterm.subst_size_lt (head_succ_strict_p n) σ
      have hs := congrArg size heq
      omega
theorem root_shape
    {a b c : Term}
    (h : RootStep (Term.op a b) c) :
    ∃ (n : ℕ) (σ : ℕ → Term),
      a =
        Term.op
          (Term.op
            (Term.op (subst σ (head n)) b)
            b)
          (σ (n + 2)) ∧
      b = subst σ (node n).p ∧
      c = subst σ (rhs n) := by
  rcases h with ⟨n, σ, hs, ht⟩
  have hs' :
      Term.op a b =
        Term.op (subst σ (node n).A) (subst σ (node n).p) := by
    simpa [lhs] using hs
  injection hs' with ha hb
  refine ⟨n, σ, ?_, hb, ht⟩
  calc
    a = subst σ (node n).A := ha
    _ = subst σ (Term.op (core n) (.var (n + 2))) := by
          rw [A_shape]
    _ =
        Term.op
          (Term.op
            (Term.op (subst σ (head n)) (subst σ (node n).p))
            (subst σ (node n).p))
          (σ (n + 2)) := by
          rfl
    _ =
        Term.op
          (Term.op
            (Term.op (subst σ (head n)) b)
            b)
          (σ (n + 2)) := by
          rw [← hb]
theorem no_root_generic_1 (x₀ y₀ : Term) :
    ¬ ∃ c : Term, RootStep (Term.op (Term.op y₀ x₀) y₀) c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  injection ha with hleft hright
  have hs := congrArg size hleft
  simp only [size_op] at hs
  omega
theorem no_root_generic_2 (x₀ y₀ : Term) :
    ¬ ∃ c : Term,
      RootStep (Term.op (Term.op (Term.op y₀ x₀) y₀) y₀) c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  injection ha with hleft hright
  injection hleft with hleft' hright'
  have hs := congrArg size hleft'
  simp only [size_op] at hs
  omega
theorem no_root_generic_3 (x₀ y₀ z₀' : Term) :
    ¬ ∃ c : Term,
      RootStep
        (Term.op (Term.op (Term.op (Term.op y₀ x₀) y₀) y₀) z₀')
        c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  injection ha with h1 hlast
  injection h1 with h2 hyz
  injection h2 with hyHead hxz
  have hHeadP :
      subst σ (head n) = subst σ (node n).p := by
    calc
      subst σ (head n) = y₀ := hyHead.symm
      _ = z₀' := hyz
      _ = subst σ (node n).p := hb
  exact head_ne_p_subst n σ hHeadP
theorem no_root_promote_1
    {q A : Term}
    (hqa : size q < size A) :
    ¬ ∃ c : Term, RootStep (Term.op q A) c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  have hs := congrArg size ha
  simp only [size_op] at hs
  omega
theorem no_root_promote_2
    {q A : Term}
    (hqa : size q < size A) :
    ¬ ∃ c : Term,
      RootStep (Term.op (Term.op q A) A) c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  injection ha with hleft hright
  have hs := congrArg size hleft
  simp only [size_op] at hs
  omega
theorem no_root_promote_3
    {q A z₀' : Term}
    (hqa : size q < size A) :
    ¬ ∃ c : Term,
      RootStep (Term.op (Term.op (Term.op q A) A) z₀') c := by
  rintro ⟨c, hc⟩
  rcases root_shape hc with ⟨n, σ, ha, hb, ht⟩
  injection ha with h1 h4
  injection h1 with h2 hAz
  have hq :
      q = Term.op (subst σ (head n)) A := by
    calc
      q = Term.op (subst σ (head n)) z₀' := h2
      _ = Term.op (subst σ (head n)) A := by rw [← hAz]
  have hs := congrArg size hq
  simp only [size_op] at hs
  omega
theorem A_eq_head_p_eq
    {n m : ℕ}
    {σ τ : ℕ → Term}
    (hA :
      subst σ (node n).A =
        subst τ (node m).A) :
    subst σ (head n) = subst τ (head m) ∧
    subst σ (node n).p = subst τ (node m).p := by
  have hshape :
      Term.op
          (Term.op
            (Term.op (subst σ (head n)) (subst σ (node n).p))
            (subst σ (node n).p))
          (σ (n + 2))
        =
      Term.op
          (Term.op
            (Term.op (subst τ (head m)) (subst τ (node m).p))
            (subst τ (node m).p))
          (τ (m + 2)) := by
    simpa [A_shape, core, subst] using hA
  injection hshape with hcore hz
  injection hcore with hpref hp
  injection hpref with hh hp'
  exact ⟨hh, hp⟩
theorem root_functional
    {s t u : Term}
    (ht : RootStep s t)
    (hu : RootStep s u) :
    t = u := by
  rcases ht with ⟨n, σ, hs, htout⟩
  rcases hu with ⟨m, τ, hs', huout⟩
  rw [htout, huout]
  have hL :
      subst σ (lhs n) = subst τ (lhs m) :=
    hs.symm.trans hs'
  have hL' :
      Term.op (subst σ (node n).A) (subst σ (node n).p) =
        Term.op (subst τ (node m).A) (subst τ (node m).p) := by
    simpa [lhs] using hL
  injection hL' with hA hp
  cases n with
  | zero =>
      cases m with
      | zero =>
          have hh := (A_eq_head_p_eq hA).1
          have hh' :
              Term.op (subst σ y) (subst σ x) =
                Term.op (subst τ y) (subst τ x) := by
            simpa [head] using hh
          injection hh' with hy hx
      | succ m =>
          have hhpp := A_eq_head_p_eq hA
          have hlt₁ :=
            StrictSubterm.subst_size_lt p0_strict_head0 σ
          have hlt₂ :=
            StrictSubterm.subst_size_lt
              (head_succ_strict_p m) τ
          have eh := congrArg size hhpp.1
          have ep := congrArg size hhpp.2
          omega
  | succ n =>
      cases m with
      | zero =>
          have hhpp := A_eq_head_p_eq hA
          have hlt₁ :=
            StrictSubterm.subst_size_lt
              (head_succ_strict_p n) σ
          have hlt₂ :=
            StrictSubterm.subst_size_lt p0_strict_head0 τ
          have eh := congrArg size hhpp.1
          have ep := congrArg size hhpp.2
          omega
      | succ m =>
          have hprevA :
              subst σ (node n).A =
                subst τ (node m).A := by
            simpa [node, advance] using hp
          have hprevP := (A_eq_head_p_eq hprevA).2
          simpa [rhs, node, advance] using hprevP
def VarsLt (N : ℕ) : Term → Prop
  | .var k => k < N
  | Term.op a b => VarsLt N a ∧ VarsLt N b
theorem VarsLt.mono
    {N M : ℕ}
    (hNM : N ≤ M)
    {t : Term}
    (ht : VarsLt N t) :
    VarsLt M t := by
  induction t with
  | var k =>
      simp only [VarsLt] at ht ⊢
      omega
  | op a b iha ihb =>
      simp only [VarsLt] at ht ⊢
      exact ⟨iha ht.1, ihb ht.2⟩
theorem node_bounded :
    ∀ n : ℕ,
      VarsLt (n + 3) (node n).A ∧
      VarsLt (n + 3) (node n).p ∧
      VarsLt (n + 3) (rhs n) := by
  intro n
  induction n with
  | zero =>
      simp [VarsLt, node, node0, A0, rhs, x, y, z0]
  | succ n ih =>
      have hA :
          VarsLt (n + 4) (node n).A :=
        VarsLt.mono (by omega) ih.1
      have hp :
          VarsLt (n + 4) (node n).p :=
        VarsLt.mono (by omega) ih.2.1
      have hq :
          VarsLt (n + 4) (rhs n) :=
        VarsLt.mono (by omega) ih.2.2
      simp only [node, advance, rhs, VarsLt]
      constructor
      · exact
          ⟨⟨⟨hq, hA⟩, hA⟩, by omega⟩
      · exact ⟨hA, hp⟩
theorem subst_eq_of_VarsLt
    {N : ℕ}
    {t : Term}
    (ht : VarsLt N t)
    {σ τ : ℕ → Term}
    (hστ : ∀ k : ℕ, k < N → σ k = τ k) :
    subst σ t = subst τ t := by
  induction t with
  | var k =>
      simp only [VarsLt] at ht
      simp [subst, hστ k ht]
  | op a b iha ihb =>
      simp only [VarsLt] at ht
      simp [subst, iha ht.1, ihb ht.2]
def override (σ : ℕ → Term) (k : ℕ) (v : Term) : ℕ → Term :=
  fun j => if j = k then v else σ j
theorem override_agrees_below
    (σ : ℕ → Term)
    (k : ℕ)
    (v : Term)
    {j : ℕ}
    (hj : j < k) :
    override σ k v j = σ j := by
  simp [override, Nat.ne_of_lt hj]
theorem promote_root
    {y₀ x₀ q₀ z₀' : Term}
    (hroot : RootStep (Term.op y₀ x₀) q₀) :
    RootStep
      (Term.op
        (Term.op
          (Term.op
            (Term.op q₀ y₀)
            y₀)
          z₀')
        y₀)
      x₀ := by
  rcases hroot with ⟨n, σ, hs, hq⟩
  have hs' :
      Term.op y₀ x₀ =
        Term.op (subst σ (node n).A) (subst σ (node n).p) := by
    simpa [lhs] using hs
  injection hs' with hy hx
  let τ : ℕ → Term := override σ (n + 3) z₀'
  have hAτ :
      subst τ (node n).A = subst σ (node n).A := by
    apply subst_eq_of_VarsLt (node_bounded n).1
    intro k hk
    exact override_agrees_below σ (n + 3) z₀' hk
  have hpτ :
      subst τ (node n).p = subst σ (node n).p := by
    apply subst_eq_of_VarsLt (node_bounded n).2.1
    intro k hk
    exact override_agrees_below σ (n + 3) z₀' hk
  have hqτ :
      subst τ (rhs n) = subst σ (rhs n) := by
    apply subst_eq_of_VarsLt (node_bounded n).2.2
    intro k hk
    exact override_agrees_below σ (n + 3) z₀' hk
  have hqτ_node :
      subst τ (node n).q = subst σ (node n).q := by
    simpa [rhs] using hqτ
  refine ⟨n + 1, τ, ?_, ?_⟩
  · simp only [lhs, node, advance, subst_op, subst_var]
    rw [hAτ, hqτ_node]
    rw [← hy]
    have hq' : q₀ = subst σ (node n).q := by
      simpa [rhs] using hq
    rw [← hq']
    simp [τ, override]
  · simp only [rhs, node, advance]
    rw [hpτ]
    exact hx
theorem base_root (x₀ y₀ z₀' : Term) :
    RootStep
      (Term.op
        (Term.op
          (Term.op
            (Term.op
              (Term.op y₀ x₀)
              y₀)
            y₀)
          z₀')
        y₀)
      x₀ := by
  let σ : ℕ → Term := fun k =>
    if k = 0 then x₀
    else if k = 1 then y₀
    else if k = 2 then z₀'
    else .var k
  refine ⟨0, σ, ?_, ?_⟩
  · simp [lhs, node, node0, A0, x, y, z0, subst, σ]
  · simp [rhs, node, node0, x, σ]
theorem normal_subterm
    {a b : Term}
    (hb : Normal Step b)
    (hab : Subterm a b) :
    Normal Step a := by
  induction hab with
  | refl =>
      exact hb
  | left hsub ih =>
      apply ih
      intro a' ha'
      exact hb (Step.left ha')
  | right hsub ih =>
      apply ih
      intro b' hb'
      exact hb (Step.right hb')
theorem root_rhs_subterm_left
    {a b c : Term}
    (h : RootStep (Term.op a b) c) :
    Subterm c a := by
  rcases h with ⟨n, σ, hs, ht⟩
  have hs' :
      Term.op a b =
        Term.op (subst σ (node n).A) (subst σ (node n).p) := by
    simpa [lhs] using hs
  injection hs' with ha hb
  have hsub :
      Subterm (subst σ (rhs n)) (subst σ (node n).A) :=
    Subterm.subst_preserves (q_subterm_A n) σ
  rw [← ht, ← ha] at hsub
  exact hsub
theorem root_reduct_normal
    {a b c : Term}
    (ha : Normal Step a)
    (h : RootStep (Term.op a b) c) :
    Normal Step c :=
  normal_subterm ha (root_rhs_subterm_left h)
theorem normal_op_of_no_root
    {a b : Term}
    (ha : Normal Step a)
    (hb : Normal Step b)
    (hroot : ¬ ∃ c : Term, RootStep (Term.op a b) c) :
    Normal Step (Term.op a b) := by
  intro t ht
  cases ht with
  | root hr =>
      exact hroot ⟨t, hr⟩
  | left h =>
      exact ha h
  | right h =>
      exact hb h
abbrev NTerm : Type :=
  {t : Term // Normal Step t}
noncomputable def nmul (a b : NTerm) : NTerm := by
  classical
  by_cases h : ∃ c : Term, RootStep (Term.op a.1 b.1) c
  · let c : Term := Classical.choose h
    exact
      ⟨c,
        root_reduct_normal a.2
          (Classical.choose_spec h)⟩
  · exact
      ⟨Term.op a.1 b.1,
        normal_op_of_no_root a.2 b.2 h⟩
theorem nmul_val_of_root
    {a b : NTerm}
    {c : Term}
    (h : RootStep (Term.op a.1 b.1) c) :
    (nmul a b).1 = c := by
  classical
  unfold nmul
  split
  · next hExists =>
      exact
        root_functional
          (Classical.choose_spec hExists)
          h
  · next hNone =>
      exact False.elim (hNone ⟨c, h⟩)
theorem nmul_val_of_no_root
    {a b : NTerm}
    (h : ¬ ∃ c : Term, RootStep (Term.op a.1 b.1) c) :
    (nmul a b).1 = Term.op a.1 b.1 := by
  classical
  unfold nmul
  split
  · next hExists =>
      exact False.elim (h ⟨Classical.choose hExists, Classical.choose_spec hExists⟩)
  · rfl
noncomputable instance normalMagma : Magma NTerm where
  op := nmul
theorem normalModel_law40909 :
    Law40909 NTerm := by
  intro X Y Z
  change
    nmul
        (nmul
          (nmul
            (nmul
              (nmul Y X)
              Y)
            Y)
          Z)
        Y
      = X
  by_cases hfirst :
      ∃ c : Term, RootStep (Term.op Y.1 X.1) c
  · rcases hfirst with ⟨q₀, hqroot⟩
    let T1 : NTerm :=
      ⟨q₀, root_reduct_normal Y.2 hqroot⟩
    have e1 : nmul Y X = T1 := by
      apply Subtype.ext
      exact nmul_val_of_root hqroot
    have hqY : size q₀ < size Y.1 := by
      rcases hqroot with ⟨n, σ, hs, hq⟩
      have hs' :
          Term.op Y.1 X.1 =
            Term.op (subst σ (node n).A) (subst σ (node n).p) := by
        simpa [lhs] using hs
      injection hs' with hY hX
      have hlt :=
        StrictSubterm.subst_size_lt (q_strict_A n) σ
      have eqQ := congrArg size hq
      have eqY := congrArg size hY
      omega
    have h2none :
        ¬ ∃ c : Term, RootStep (Term.op q₀ Y.1) c :=
      no_root_promote_1 hqY
    let T2 : NTerm :=
      ⟨Term.op q₀ Y.1,
        normal_op_of_no_root T1.2 Y.2 h2none⟩
    have e2 : nmul T1 Y = T2 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h2none
    have h3none :
        ¬ ∃ c : Term,
          RootStep (Term.op (Term.op q₀ Y.1) Y.1) c :=
      no_root_promote_2 hqY
    let T3 : NTerm :=
      ⟨Term.op (Term.op q₀ Y.1) Y.1,
        normal_op_of_no_root T2.2 Y.2 h3none⟩
    have e3 : nmul T2 Y = T3 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h3none
    have h4none :
        ¬ ∃ c : Term,
          RootStep
            (Term.op (Term.op (Term.op q₀ Y.1) Y.1) Z.1)
            c :=
      no_root_promote_3 hqY
    let T4 : NTerm :=
      ⟨Term.op (Term.op (Term.op q₀ Y.1) Y.1) Z.1,
        normal_op_of_no_root T3.2 Z.2 h4none⟩
    have e4 : nmul T3 Z = T4 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h4none
    have hfinal :
        RootStep
          (Term.op T4.1 Y.1)
          X.1 := by
      simpa [T4] using promote_root hqroot
    have e5 : nmul T4 Y = X := by
      apply Subtype.ext
      exact nmul_val_of_root hfinal
    rw [e1, e2, e3, e4, e5]
  · let T1 : NTerm :=
      ⟨Term.op Y.1 X.1,
        normal_op_of_no_root Y.2 X.2 hfirst⟩
    have e1 : nmul Y X = T1 := by
      apply Subtype.ext
      exact nmul_val_of_no_root hfirst
    have h2none :
        ¬ ∃ c : Term,
          RootStep (Term.op (Term.op Y.1 X.1) Y.1) c :=
      no_root_generic_1 X.1 Y.1
    let T2 : NTerm :=
      ⟨Term.op (Term.op Y.1 X.1) Y.1,
        normal_op_of_no_root T1.2 Y.2 h2none⟩
    have e2 : nmul T1 Y = T2 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h2none
    have h3none :
        ¬ ∃ c : Term,
          RootStep
            (Term.op (Term.op (Term.op Y.1 X.1) Y.1) Y.1)
            c :=
      no_root_generic_2 X.1 Y.1
    let T3 : NTerm :=
      ⟨Term.op (Term.op (Term.op Y.1 X.1) Y.1) Y.1,
        normal_op_of_no_root T2.2 Y.2 h3none⟩
    have e3 : nmul T2 Y = T3 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h3none
    have h4none :
        ¬ ∃ c : Term,
          RootStep
            (Term.op
              (Term.op (Term.op (Term.op Y.1 X.1) Y.1) Y.1)
              Z.1)
            c :=
      no_root_generic_3 X.1 Y.1 Z.1
    let T4 : NTerm :=
      ⟨Term.op
          (Term.op (Term.op (Term.op Y.1 X.1) Y.1) Y.1)
          Z.1,
        normal_op_of_no_root T3.2 Z.2 h4none⟩
    have e4 : nmul T3 Z = T4 := by
      apply Subtype.ext
      exact nmul_val_of_no_root h4none
    have hfinal :
        RootStep (Term.op T4.1 Y.1) X.1 := by
      simpa [T4] using base_root X.1 Y.1 Z.1
    have e5 : nmul T4 Y = X := by
      apply Subtype.ext
      exact nmul_val_of_root hfinal
    rw [e1, e2, e3, e4, e5]
def normalVar (k : ℕ) : NTerm :=
  ⟨.var k, var_normal k⟩
theorem normalModel_nontrivial :
    (normalVar 0 : NTerm) ≠ normalVar 1 := by
  intro h
  have hv :
      (.var 0 : Term) = .var 1 :=
    congrArg Subtype.val h
  injection hv with hk
  omega
theorem normalModel_not_law28770 :
    ¬ Law28770 NTerm :=
  not_law28770_of_nontrivial
    normalModel_law40909
    normalModel_nontrivial
theorem direct_FALSE_certificate :
    ∃ (G : Type) (_ : Magma G),
      Law40909 G ∧ ¬ Law28770 G :=
  ⟨NTerm, normalMagma,
    normalModel_law40909,
    normalModel_not_law28770⟩
end
end ClosedForest
end ForestTerm
end Eq40909ForestCompletion
