import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.LocalHeights.Cofaces
import Mathlib.Data.Set.Card

/-!
# Crossing degrees from original triangle cofaces

The two actual incident triangles at a strictly crossing source edge
produce exactly two graph neighbors, with no global scalar height and
no assumed section degree.
-/

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [AddCommGroup E] [Module ℝ E] [DecidableEq E]

/-- Two original cofaces give exactly two neighbors at each strict
crossing label, also in the presence of multiple marked zero vertices. -/
theorem triangleSliceGraph_crossing_two_neighbors (K : SimplicialComplex ℝ E)
    {A : Finset E → E →ᵃ[ℝ] ℝ} (hA : K.CompatibleTriangleZeroSets A)
    (hcofaces : ∀ e : K.triangleCrossingEdges A,
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}.ncard = 2)
    (e : K.triangleCrossingEdges A) :
    ((K.triangleSliceGraph A).neighborSet (.inr e)).ncard = 2 := by
  classical
  obtain ⟨t, u, htu, hset⟩ := Set.ncard_eq_two.mp (hcofaces e)
  have ht : t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t := by
    change t ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert _ _
  have hu : u ∈ K.faces ∧ u.card = 3 ∧ e.val ⊆ u := by
    change u ∈ {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t}
    rw [hset]
    exact mem_insert_of_mem _ (mem_singleton _)
  obtain ⟨v, hv, hvuniq⟩ := K.existsUnique_triangleSlice_neighbor_of_coface
    hA e ht.1 ht.2.1 ht.2.2
  obtain ⟨w, hw, hwuniq⟩ := K.existsUnique_triangleSlice_neighbor_of_coface
    hA e hu.1 hu.2.1 hu.2.2
  have hvw : v ≠ w := by
    intro h
    subst w
    exact htu (hv.symm.trans hw)
  have hneighbors : (K.triangleSliceGraph A).neighborSet (.inr e) = {v, w} := by
    ext k
    change (e.val ∪ K.triangleSliceOriginalVertices A k ∈ K.faces ∧
      (e.val ∪ K.triangleSliceOriginalVertices A k).card = 3) ↔ k ∈ ({v, w} : Set _)
    constructor
    · intro hk
      have hkcoface : e.val ∪ K.triangleSliceOriginalVertices A k ∈
          {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e.val ⊆ t} :=
        ⟨hk.1, hk.2, Finset.subset_union_left⟩
      rw [hset] at hkcoface
      rcases mem_insert_iff.mp hkcoface with hkt | hku
      · exact Or.inl (hvuniq k hkt)
      · exact Or.inr (hwuniq k (mem_singleton_iff.mp hku))
    · rintro (rfl | rfl)
      · rw [hv]
        exact ⟨ht.1, ht.2.1⟩
      · rw [hw]
        exact ⟨hu.1, hu.2.1⟩
  rw [hneighbors]
  exact ncard_pair hvw

end Geometry.SimplicialComplex
