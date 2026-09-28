import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Constructions



set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

theorem coordinate_rim_intersection
    {C Q X : Type*} [TopologicalSpace C] [TopologicalSpace Q] [TopologicalSpace X]
    {S : Set X} (h : (C × C) ≃ₜ S) (q : Bool → Q ≃ₜ C) (a : C)
    (rim : Bool → Q → X)
    (hfalse : ∀ z, rim false z = (h (q false z, a) : X))
    (htrue : ∀ z, rim true z = (h (a, q true z) : X)) :
    range (rim false) ∩ range (rim true) = {(h (a, a) : X)} ∧
      ∃! z : Q × Q, rim false z.1 = rim true z.2 := by
  have heq (x y : Q) : rim false x = rim true y ↔
      x = (q false).symm a ∧ y = (q true).symm a := by
    rw [hfalse, htrue]
    constructor
    · intro hxy
      have hpair := h.injective (Subtype.ext hxy)
      exact ⟨(q false).injective ((congrArg Prod.fst hpair).trans
        ((q false).apply_symm_apply a).symm),
        (q true).injective ((congrArg Prod.snd hpair).symm.trans
        ((q true).apply_symm_apply a).symm)⟩
    · rintro ⟨rfl, rfl⟩
      rw [(q false).apply_symm_apply, (q true).apply_symm_apply]
  constructor
  · apply Subset.antisymm
    · rintro x ⟨⟨u, hu⟩, ⟨v, hv⟩⟩
      have huv := (heq u v).mp (hu.trans hv.symm)
      rw [← hu, hfalse, huv.1, (q false).apply_symm_apply]
      exact mem_singleton _
    · intro x hx
      rcases mem_singleton_iff.mp hx with rfl
      exact ⟨⟨(q false).symm a, by rw [hfalse, (q false).apply_symm_apply]⟩,
        ⟨(q true).symm a, by rw [htrue, (q true).apply_symm_apply]⟩⟩
  · refine ⟨((q false).symm a, (q true).symm a), (heq _ _).mpr ⟨rfl, rfl⟩, ?_⟩
    intro z hz
    exact Prod.ext ((heq z.1 z.2).mp hz).1 ((heq z.1 z.2).mp hz).2

end PoincareConjecture.M76
