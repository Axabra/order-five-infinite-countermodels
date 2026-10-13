import JudgeProblem
import Mathlib.Tactic

namespace submission
namespace C

inductive T where
  | var : ℕ → T
  | op : T → T → T
deriving DecidableEq, Repr

open T

def sz : T → ℕ
  | .var _ => 1
  | .op a b => sz a + sz b + 1

@[simp] theorem sz_var (n : ℕ) : sz (.var n) = 1 := rfl
@[simp] theorem sz_op (a b : T) : sz (.op a b) = sz a + sz b + 1 := rfl

def baseLink (c q : T) : Bool :=
  match q with
  | .op _ c' => decide (c' = c)
  | _ => false

def linked (c q : T) : Bool :=
  match baseLink c q with
  | true => true
  | false =>
      match c with
      | .op (.op q' r) (.op a b) =>
          if hq : q' = q then
            if hab : a = b then linked q' r else false
          else false
      | _ => false
termination_by sz c
decreasing_by
  simp [sz]
  omega

@[simp] theorem linked_base (c z : T) :
    linked c (.op z c) = true := by
  cases c with
  | var n =>
      simp [linked, baseLink]
  | op u v =>
      cases u with
      | var n =>
          simp [linked, baseLink]
      | op q r =>
          cases v with
          | var n =>
              simp [linked, baseLink]
          | op a b =>
              simp [linked, baseLink]

theorem linked_step {c q a : T}
    (h : linked c q = true) :
    linked (.op (.op c q) (.op a a)) c = true := by
  cases hb : baseLink (.op (.op c q) (.op a a)) c <;>
    simp [linked, hb, h]

theorem baseLink_shape {c q : T}
    (h : baseLink c q = true) :
    ∃ z : T, q = .op z c := by
  cases q with
  | var n => simp [baseLink] at h
  | op z c' =>
      have hc : c' = c := by
        simpa [baseLink] using h
      subst c'
      exact ⟨z, rfl⟩

theorem linked_shape {c q : T}
    (h : linked c q = true) :
    (∃ z : T, q = .op z c) ∨
    (∃ r a : T,
      c = .op (.op q r) (.op a a) ∧
      linked q r = true) := by
  cases hb : baseLink c q with
  | true =>
      exact Or.inl (baseLink_shape hb)
  | false =>
      cases c with
      | var n => simp [linked, hb] at h
      | op u v =>
          cases u with
          | var n => simp [linked, hb] at h
          | op q' r =>
              cases v with
              | var n => simp [linked, hb] at h
              | op a b =>
                  by_cases hq : q' = q
                  · by_cases hab : a = b
                    · have hr : linked q r = true := by
                        subst q'
                        subst b
                        simpa [linked, hb] using h
                      subst q'
                      subst b
                      exact Or.inr ⟨r, a, rfl, hr⟩
                    · subst q'
                      have hf : False := by
                        simpa [linked, hb, hab] using h
                      exact False.elim hf
                  · simp [linked, hb, hq] at h

theorem linked_size_ne {c q : T}
    (h : linked c q = true) :
    sz c ≠ sz q := by
  rcases linked_shape h with hbase | hstep
  · rcases hbase with ⟨z, rfl⟩
    simp [sz]
    omega
  · rcases hstep with ⟨r, a, rfl, _⟩
    simp [sz]
    omega

def root (a b : T) : Option T :=
  match b with
  | .op (.op c q) (.op a1 a2) =>
      if h1 : a1 = a then
        if h2 : a2 = a then
          match linked c q with
          | true => some c
          | false => none
        else none
      else none
  | _ => none

theorem root_shape {a b c : T}
    (h : root a b = some c) :
    ∃ q : T,
      b = .op (.op c q) (.op a a) ∧
      linked c q = true := by
  cases b with
  | var n => simp [root] at h
  | op u v =>
      cases u with
      | var n => simp [root] at h
      | op c0 q =>
          cases v with
          | var n => simp [root] at h
          | op a1 a2 =>
              by_cases h1 : a1 = a
              · by_cases h2 : a2 = a
                · cases hl : linked c0 q with
                  | false => simp [root, h1, h2, hl] at h
                  | true =>
                      have hc : c0 = c := by
                        simpa [root, h1, h2, hl] using h
                      subst c
                      subst a1
                      subst a2
                      exact ⟨q, rfl, hl⟩
                · simp [root, h1, h2] at h
              · simp [root, h1] at h

theorem root_out_lt {a b c : T}
    (h : root a b = some c) :
    sz c < sz b := by
  rcases root_shape h with ⟨q, rfl, _⟩
  simp [sz]
  omega

theorem root_none_small_right {a b : T}
    (hba : sz b < sz a) :
    root a b = none := by
  cases hr : root a b with
  | none => rfl
  | some c =>
      rcases root_shape hr with ⟨q, hb, _⟩
      have hs := congrArg sz hb
      simp [sz] at hs
      omega

theorem root_diag (a : T) :
    root a a = none := by
  cases hr : root a a with
  | none => rfl
  | some c =>
      rcases root_shape hr with ⟨q, ha, _⟩
      have hs := congrArg sz ha
      simp [sz] at hs
      omega

theorem root_x_zx (x z : T) :
    root x (.op z x) = none := by
  cases hr : root x (.op z x) with
  | none => rfl
  | some c =>
      rcases root_shape hr with ⟨q, hs, _⟩
      injection hs with hleft hright
      have hz := congrArg sz hright
      simp [sz] at hz
      omega

theorem root_c_yy (c y : T) :
    root c (.op y y) = none := by
  cases hr : root c (.op y y) with
  | none => rfl
  | some d =>
      rcases root_shape hr with ⟨q, hs, hl⟩
      injection hs with hleft hright
      have heq : T.op d q = T.op c c := hleft.symm.trans hright
      injection heq with hd hq
      subst d
      subst q
      exact False.elim ((linked_size_ne hl) rfl)

theorem root_linked {a b c : T}
    (h : root a b = some c) :
    linked b c = true := by
  rcases root_shape h with ⟨q, rfl, hl⟩
  exact linked_step hl

@[simp] theorem root_base (x y z : T) :
    root y (.op (.op x (.op z x)) (.op y y)) = some x := by
  simp [root, linked_base]

theorem root_promote {z x q : T}
    (h : root z x = some q)
    (y : T) :
    root y (.op (.op x q) (.op y y)) = some x := by
  have hl : linked x q = true := root_linked h
  simp [root, hl]

def mul (a b : T) : T :=
  match root a b with
  | some c => c
  | none => .op a b

instance mg : Magma T where
  op := mul

@[simp] theorem mul_right_var (a : T) (k : ℕ) :
    mul a (.var k) = .op a (.var k) := rfl

@[simp] theorem mul_pair_left_var (a : T) (k : ℕ) (b : T) :
    mul a (.op (.var k) b) = .op a (.op (.var k) b) := rfl

theorem law11116 :
    ∀ x y z : T,
      mul y (mul (mul x (mul z x)) (mul y y)) = x := by
  intro x y z
  cases hzx : root z x with
  | none =>
      have ezx : mul z x = .op z x := by
        simp [mul, hzx]
      have hxzx : root x (.op z x) = none := root_x_zx x z
      have exzx : mul x (.op z x) = .op x (.op z x) := by
        simp [mul, hxzx]
      have hyy : root y y = none := root_diag y
      have eyy : mul y y = .op y y := by
        simp [mul, hyy]
      have hmid : root (.op x (.op z x)) (.op y y) = none :=
        root_c_yy (.op x (.op z x)) y
      have emid :
          mul (.op x (.op z x)) (.op y y) =
            .op (.op x (.op z x)) (.op y y) := by
        simp [mul, hmid]
      have hfinal := root_base x y z
      rw [ezx, exzx, eyy, emid]
      simp [mul, hfinal]
  | some q =>
      have ezx : mul z x = q := by
        simp [mul, hzx]
      have hqx : sz q < sz x := root_out_lt hzx
      have hxq : root x q = none := root_none_small_right hqx
      have exq : mul x q = .op x q := by
        simp [mul, hxq]
      have hyy : root y y = none := root_diag y
      have eyy : mul y y = .op y y := by
        simp [mul, hyy]
      have hmid : root (.op x q) (.op y y) = none :=
        root_c_yy (.op x q) y
      have emid :
          mul (.op x q) (.op y y) =
            .op (.op x q) (.op y y) := by
        simp [mul, hmid]
      have hfinal : root y (.op (.op x q) (.op y y)) = some x :=
        root_promote hzx y
      rw [ezx, exq, eyy, emid]
      simp [mul, hfinal]

end C


namespace C

def Law28770 : Prop :=
  ∀ x y z : T,
    mul (mul (mul (mul y y) y) x) (mul y z) = x

theorem not28770 : ¬ Law28770 := by
  intro h
  have hh := h (.var 0) (.var 1) (.var 2)
  change
    T.op
      (T.op
        (T.op (T.op (.var 1) (.var 1)) (.var 1))
        (.var 0))
      (T.op (.var 1) (.var 2)) =
    .var 0 at hh
  cases hh

end C
end submission

open submission.C

def submission : Goal := by
  refine ⟨submission.C.T, submission.C.mg, ?_, ?_⟩
  · intro x y z
    exact (submission.C.law11116 x y z).symm
  · intro h28770
    apply submission.C.not28770
    intro x y z
    exact (h28770 x y z).symm
