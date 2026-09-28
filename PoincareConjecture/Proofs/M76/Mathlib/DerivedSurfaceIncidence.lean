import PoincareConjecture.Proofs.M76.Mathlib.DerivedFaceChainIncidence
import PoincareConjecture.Proofs.M76.Mathlib.SurfaceFaceChainCount









set_option autoImplicit false

open Set
open scoped BigOperators

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  (K : SimplicialComplex ℝ E) [Fintype K.faces]
  (c : K.faces → E)
  (hc : ∀ s : K.faces, ∃ w : E → ℝ, (∀ v ∈ s.val, 0 < w v) ∧
    (∑ v ∈ s.val, w v) = 1 ∧ (∑ v ∈ s.val, w v • v) = c s)





theorem derivedSubdivision_two_triangle_cofaces
    (hbound : ∀ u ∈ K.faces, u.card ≤ 3)
    (hcofaces : ∀ e ∈ K.faces, e.card = 2 →
      {u : Finset E | u ∈ K.faces ∧ u.card = 3 ∧ e ⊆ u}.ncard = 2) :
    ∀ e ∈ (K.derivedSubdivision c hc).faces, e.card = 2 →
      {u : Finset E | u ∈ (K.derivedSubdivision c hc).faces ∧
        u.card = 3 ∧ e ⊆ u}.ncard = 2 := by
  classical
  have hcount (s t : K.faces) (hst : s < t) :
      {u : Finset E | u ∈ (K.derivedSubdivision c hc).faces ∧
        u.card = 3 ∧ {c s, c t} ⊆ u}.ncard = 2 := by
    rw [K.ncard_derived_edge_cofaces c hc hst]
    have hraw : {u : K.faces | u ≠ s ∧ u ≠ t ∧
        (u ≤ s ∨ s ≤ u) ∧ (u ≤ t ∨ t ≤ u)}.ncard =
        {u : Finset E | u ∈ K.faces ∧ u ≠ s.val ∧ u ≠ t.val ∧
          (u ⊆ s.val ∨ s.val ⊆ u) ∧ (u ⊆ t.val ∨ t.val ⊆ u)}.ncard := by
      apply ncard_congr (fun u _ => u.val)
      · rintro u ⟨hus, hut, hsu, htu⟩
        exact ⟨u.property, fun h => hus (Subtype.ext h),
          fun h => hut (Subtype.ext h), hsu, htu⟩
      · intro u v _ _ h
        exact Subtype.ext h
      · rintro u ⟨hu, hus, hut, hsu, htu⟩
        refine ⟨⟨u, hu⟩, ⟨?_, ?_, hsu, htu⟩, rfl⟩
        · intro h
          exact hus (congrArg Subtype.val h)
        · intro h
          exact hut (congrArg Subtype.val h)
    rw [hraw]
    exact K.ncard_surface_face_chain_extensions hbound hcofaces s.property t.property hst
  intro e he hec
  obtain ⟨a, _, hchain, rfl⟩ := (K.derivedSubdivision_faces c hc e).mp he
  have hac : a.card = 2 :=
    (Finset.card_image_of_injective a (K.positiveFaceCenter_injective c hc)).symm.trans hec
  obtain ⟨s, t, hst, rfl⟩ := Finset.card_eq_two.mp hac
  have hcomp := hchain s (by simp) t (by simp)
  simp only [Finset.image_insert, Finset.image_singleton]
  rcases hcomp with h | h
  · exact hcount s t (lt_iff_le_not_ge.mpr ⟨h, fun h' => hst (le_antisymm h h')⟩)
  · rw [Finset.pair_comm]
    exact hcount t s (lt_iff_le_not_ge.mpr ⟨h, fun h' => hst (le_antisymm h' h)⟩)

end Geometry.SimplicialComplex
