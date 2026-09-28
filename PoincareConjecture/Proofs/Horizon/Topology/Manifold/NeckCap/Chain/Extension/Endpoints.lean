import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Chain




set_option autoImplicit false

open Set

namespace PoincareConjecture.ChainShape

def extendLeft : ChainShape → ChainShape
  | .finite a b => .finite (a - 1) b
  | .forward a => .forward (a - 1)
  | .backward b => .backward b
  | .biInfinite => .biInfinite

def extendRight : ChainShape → ChainShape
  | .finite a b => .finite a (b + 1)
  | .forward a => .forward a
  | .backward b => .backward (b + 1)
  | .biInfinite => .biInfinite

theorem le_of_left_endpoint {shape : ChainShape} {a : ℤ}
    (ha : a ∈ shape.active) (hprev : a - 1 ∉ shape.active)
    {i : ℤ} (hi : i ∈ shape.active) : a ≤ i := by
  cases shape <;> simp_all only [active, mem_Icc, mem_Ici, mem_Iic, mem_univ,
    not_true_eq_false] <;> omega

theorem le_of_right_endpoint {shape : ChainShape} {b : ℤ}
    (hb : b ∈ shape.active) (hnext : b + 1 ∉ shape.active)
    {i : ℤ} (hi : i ∈ shape.active) : i ≤ b := by
  cases shape <;> simp_all only [active, mem_Icc, mem_Ici, mem_Iic, mem_univ,
    not_true_eq_false] <;> omega

theorem extendLeft_active {shape : ChainShape} {a : ℤ}
    (ha : a ∈ shape.active) (hprev : a - 1 ∉ shape.active) :
    shape.extendLeft.active = insert (a - 1) shape.active := by
  cases shape <;> ext i <;>
    simp_all only [extendLeft, active, mem_Icc, mem_Ici, mem_Iic, mem_univ,
      mem_insert_iff, not_true_eq_false] <;> omega

theorem extendRight_active {shape : ChainShape} {b : ℤ}
    (hb : b ∈ shape.active) (hnext : b + 1 ∉ shape.active) :
    shape.extendRight.active = insert (b + 1) shape.active := by
  cases shape <;> ext i <;>
    simp_all only [extendRight, active, mem_Icc, mem_Ici, mem_Iic, mem_univ,
      mem_insert_iff, not_true_eq_false] <;> omega

end PoincareConjecture.ChainShape
