import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Faces.NormalCornerAdjacency
import Mathlib.Data.Set.Card

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.TriangleCorner

theorem corner_order_cardinality
    {ι : Type*} [Finite ι] (c : ι → Fin 3) (a : ι → ℝ)
    (hinj : ∀ i j, c i = c j → a i = a j → i = j) :
    Nat.card {i : ι // ∃ j, c j = c i ∧ a i < a j} + Nat.card (range c) = Nat.card ι ∧
      Nat.card (range c) ≤ 3 := by
  classical
  let := Fintype.ofFinite ι
  let Good : Set ι := {i | ∃ j, c j = c i ∧ a i < a j}
  let f : (Goodᶜ : Set ι) → range c := fun i => ⟨c i, mem_range_self _⟩
  have hmax (i : (Goodᶜ : Set ι)) (j : ι) (hji : c j = c i) : a j ≤ a i := by
    by_contra hn
    exact i.property ⟨j, hji, lt_of_not_ge hn⟩
  have hfinj : Function.Injective f := by
    intro i j he
    have hc : c i = c j := congrArg Subtype.val he
    apply Subtype.ext
    exact hinj i j hc (le_antisymm (hmax j i hc) (hmax i j hc.symm))
  have hfsurj : Function.Surjective f := by
    rintro ⟨d, hd⟩
    obtain ⟨i, hi⟩ := hd
    let s := Finset.univ.filter fun k => c k = d
    have hs : s.Nonempty := ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
    obtain ⟨j, hj, hmaxj⟩ := s.exists_max_image a hs
    have hjc : c j = d := (Finset.mem_filter.mp hj).2
    have hjnot : j ∈ Goodᶜ := by
      rintro ⟨k, hk, hjk⟩
      exact (not_le_of_gt hjk) (hmaxj k (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hk.trans hjc⟩))
    exact ⟨⟨j, hjnot⟩, Subtype.ext hjc⟩
  have hcard : Nat.card (Goodᶜ : Set ι) = Nat.card (range c) := Nat.card_congr
    (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)
  have hsum := ncard_add_ncard_compl Good
  change Nat.card Good + Nat.card (Goodᶜ : Set ι) = Nat.card ι at hsum
  rw [hcard] at hsum
  refine ⟨hsum, ?_⟩
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective
    (Subtype.val : range c → Fin 3) Subtype.val_injective

end PoincareConjecture.M76.TriangleCorner
