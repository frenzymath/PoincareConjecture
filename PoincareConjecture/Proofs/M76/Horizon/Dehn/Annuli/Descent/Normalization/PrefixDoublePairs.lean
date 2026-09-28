import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Descent.Normalization.FiniteHistory











set_option autoImplicit false

open Set

namespace Geometry



theorem exists_active_prefix_of_double_pair
    {X Y : Type*} {n : ℕ} (P : ℕ → Set X) (F : Fin n → Set X)
    (hsucc : ∀ i : Fin n, P (i.val + 1) = P i.val ∪ F i)
    (g : X → Y) (hzero : InjOn g (P 0)) (hface : ∀ i, InjOn g (F i))
    {x y : X} (hx : x ∈ P n) (hy : y ∈ P n) (hne : x ≠ y) (hxy : g x = g y) :
    ∃ (i : Fin n) (x' y' : X),
      ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
      x' ∈ F i ∧ x' ∉ P i.val ∧ y' ∈ P i.val ∧ g x' = g y' := by
  have hbuild : ∀ m, m ≤ n → ∀ x y, x ∈ P m → y ∈ P m → x ≠ y → g x = g y →
      ∃ (i : Fin n) (x' y' : X), i.val < m ∧
        ((x' = x ∧ y' = y) ∨ (x' = y ∧ y' = x)) ∧
        x' ∈ F i ∧ x' ∉ P i.val ∧ y' ∈ P i.val ∧ g x' = g y' := by
    intro m
    induction m with
    | zero =>
      intro _ x y hx hy hne heq
      exact False.elim (hne (hzero hx hy heq))
    | succ m ih =>
      intro hmn x y hx hy hne heq
      let i : Fin n := ⟨m, by omega⟩
      have hx' : x ∈ P m ∪ F i := (hsucc i).subset hx
      have hy' : y ∈ P m ∪ F i := (hsucc i).subset hy
      by_cases hxold : x ∈ P m
      · by_cases hyold : y ∈ P m
        · obtain ⟨k, a, b, hkm, hab⟩ := ih (by omega) x y hxold hyold hne heq
          exact ⟨k, a, b, by omega, hab⟩
        · exact ⟨i, y, x, Nat.lt_succ_self _, Or.inr ⟨rfl, rfl⟩,
            hy'.resolve_left hyold, hyold, hxold, heq.symm⟩
      · by_cases hyold : y ∈ P m
        · exact ⟨i, x, y, Nat.lt_succ_self _, Or.inl ⟨rfl, rfl⟩,
            hx'.resolve_left hxold, hxold, hyold, heq⟩
        · exact False.elim (hne (hface i (hx'.resolve_left hxold) (hy'.resolve_left hyold) heq))
  obtain ⟨i, x', y', _, h⟩ := hbuild n le_rfl x y hx hy hne hxy
  exact ⟨i, x', y', h⟩

end Geometry
