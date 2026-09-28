import PoincareConjecture.Proofs.M25.Topology3D.Polygon.CyclicCut
import PoincareConjecture.Proofs.M25.Topology3D.Polygon.RegionNesting











set_option autoImplicit false

open Set

namespace PoincareConjecture.M25.Topology3D

variable {n : ℕ}


theorem cyclicArcIndex_rotate (a : Fin n) (m : ℕ) (j : Fin (m + 1))
    (hj : j ≠ Fin.last m) :
    cyclicArcIndex a m (finRotate (m + 1) j) = finRotate n (cyclicArcIndex a m j) := by
  revert hj
  refine Fin.lastCases ?_ (fun i => ?_) j
  · intro h
    exact (h rfl).elim
  · intro _
    rw [show finRotate (m + 1) i.castSucc = i.succ from finRotate_of_lt i.isLt,
      cyclicArcIndex_succ]


theorem cyclicArcIndex_rotate_symm (a : Fin n) (m : ℕ) (j : Fin (m + 1)) (hj : j ≠ 0) :
    cyclicArcIndex a m ((finRotate (m + 1)).symm j) =
      (finRotate n).symm (cyclicArcIndex a m j) := by
  have hlast : (finRotate (m + 1)).symm j ≠ Fin.last m := by
    intro h
    have heq := congrArg (finRotate (m + 1)) h
    rw [Equiv.apply_symm_apply, finRotate_last] at heq
    exact hj heq
  have h := cyclicArcIndex_rotate a m ((finRotate (m + 1)).symm j) hlast
  rw [Equiv.apply_symm_apply] at h
  simpa only [Equiv.symm_apply_apply] using (congrArg (finRotate n).symm h).symm



theorem cyclicArcIndex_internal_ne_other_edge (a b : Fin n) (hab : b ≠ a)
    (j : Fin (cyclicDistance a b + 1)) (hj0 : j ≠ 0)
    (hjlast : j ≠ Fin.last (cyclicDistance a b)) (i : Fin n)
    (hi : cyclicDistance b i < cyclicDistance b a) :
    cyclicArcIndex a (cyclicDistance a b) j ≠ i ∧
      cyclicArcIndex a (cyclicDistance a b) j ≠ finRotate n i := by
  have hinj := cyclicArcIndex_injective a (cyclicDistance_lt a b)
  have hlast : cyclicArcIndex a (cyclicDistance a b) (Fin.last (cyclicDistance a b)) = b := by
    rw [cyclicArcIndex_last, iterate_cyclicDistance]
  have hna : cyclicArcIndex a (cyclicDistance a b) j ≠ a := by
    intro h
    exact hj0 (hinj (h.trans (cyclicArcIndex_zero a _).symm))
  have hnb : cyclicArcIndex a (cyclicDistance a b) j ≠ b := by
    intro h
    exact hjlast (hinj (h.trans hlast.symm))
  have hout : cyclicArcIndex a (cyclicDistance a b) j ∉
      range (cyclicArcIndex b (cyclicDistance b a)) := by
    intro h
    have hends : cyclicArcIndex a (cyclicDistance a b) j ∈ ({a, b} : Set (Fin n)) :=
      cyclicArc_vertexIndex_inter a b hab ▸ ⟨⟨j, rfl⟩, h⟩
    exact hends.elim hna hnb
  obtain ⟨t, ht⟩ :=
    (mem_range_cyclicArcEdgeIndex_iff b _ (cyclicDistance_lt b a) i).mpr hi
  change cyclicArcIndex b (cyclicDistance b a) t.castSucc = i at ht
  have hiA : i ∈ range (cyclicArcIndex b (cyclicDistance b a)) := ⟨t.castSucc, ht⟩
  have hrA : finRotate n i ∈ range (cyclicArcIndex b (cyclicDistance b a)) := by
    refine ⟨t.succ, ?_⟩
    rw [cyclicArcIndex_succ, ht]
  exact ⟨fun h => hout (h.symm ▸ hiA), fun h => hout (h.symm ▸ hrA)⟩



theorem IsSimplePolygon.polygonCut_regions_subset {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {p : Polygon E n} (hp : IsSimplePolygon p) (a b : Fin n)
    (hq : IsSimplePolygon (polygonCut p a b)) (hdim : Module.finrank ℝ E = 2)
    (hseg : segment ℝ (p a) (p b) ⊆ closure (polygonInterior p)) :
    polygonInterior (polygonCut p a b) ⊆ polygonInterior p ∧
      closure (polygonInterior (polygonCut p a b)) ⊆ closure (polygonInterior p) := by
  apply hp.polygonRegions_subset_of_boundary_subset_closureInterior hq hdim
  rw [polygonCut_boundary]
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨i, hi⟩ := mem_iUnion.mp hx
    obtain ⟨_, hxedge⟩ := mem_iUnion.mp hi
    rw [hp.closure_polygonInterior hdim]
    exact Or.inr (polygon_edgeSet_subset_boundary p i hxedge)
  · exact hseg hx

end PoincareConjecture.M25.Topology3D
