import Mathlib

namespace Axabra.OrderSix

universe u

variable {G : Type u}

def Law11116 (op : G → G → G) : Prop :=
  ∀ x y z : G,
    op y (op (op x (op z x)) (op y y)) = x

def LawA6 (op : G → G → G) : Prop :=
  ∀ x y u v : G,
    op y (op (op x (op (op u v) x)) (op y y)) = x

theorem a6_of_e11116 (op : G → G → G) :
    Law11116 op → LawA6 op := by
  intro h x y u v
  exact h x y (op u v)

theorem surjective_of_a6 (op : G → G → G) (h : LawA6 op) :
    ∀ z : G, ∃ a b : G, op a b = z := by
  intro z
  refine ⟨z, op (op z (op (op z z) z)) (op z z), ?_⟩
  exact h z z z z

theorem e11116_of_a6 (op : G → G → G) :
    LawA6 op → Law11116 op := by
  intro h x y z
  rcases surjective_of_a6 op h z with ⟨u, v, huv⟩
  have hz := h x y u v
  rw [huv] at hz
  exact hz

theorem a6_iff_e11116 (op : G → G → G) :
    LawA6 op ↔ Law11116 op := by
  constructor
  · exact e11116_of_a6 op
  · exact a6_of_e11116 op

end Axabra.OrderSix
