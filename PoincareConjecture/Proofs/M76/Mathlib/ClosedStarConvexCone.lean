import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarConvexFrontier
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionConvexTriangulation

set_option autoImplicit false

open Set NormedSpace

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [DecidableEq E]

theorem convexJoin_closedStar_frontier_eq_inter
    (K : SimplicialComplex ℝ E) {C : Set E}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C)
    (hdisj : Disjoint C (K.link 0).space)
    (hne : ((K.closedStar 0).space ∩ frontier C).Nonempty) :
    convexJoin ℝ {0} ((K.closedStar 0).space ∩ frontier C) =
      (K.closedStar 0).space ∩ C := by
  ext x
  rw [mem_convexJoin_zero_iff]
  constructor
  · rintro ⟨y, hy, r, hr, rfl⟩
    exact ⟨K.smul_mem_closedStar_zero hy.1 hr,
      hcv.smul_mem_of_zero_mem (interior_subset hzero)
        (hC.isClosed.frontier_subset hy.2) hr⟩
  · rintro ⟨hxstar, hxC⟩
    by_cases hx0 : x = 0
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, hy, 0, ⟨le_rfl, zero_le_one⟩, by simp [hx0]⟩
    obtain ⟨z, hzC, r, hr, hxz⟩ := hC.exists_frontier_pos_smul hcv hzero hxC hx0
    obtain ⟨y, hy, t, ht, hxy⟩ := exists_linkPoint_smul hxstar hx0
    have hdir : normalize y = normalize z := by
      have he := congrArg (normalize : E → E) (hxy.symm.trans hxz)
      simpa only [normalize_smul_of_pos ht.1, normalize_smul_of_pos hr.1] using he
    have hzstar : z ∈ (K.closedStar 0).space ∩ frontier C := by
      rw [← K.radial_frontier_section_eq_closedStar_inter hC.isClosed hcv hzero hdisj]
      exact ⟨hzC, y, hy, hdir⟩
    exact ⟨z, hzstar, r, ⟨hr.1.le, hr.2⟩, hxz⟩

variable [FiniteDimensional ℝ E]

omit [DecidableEq E] in

theorem interior_space_eq_empty_of_card_le
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hcard : ∀ s ∈ K.faces, s.card ≤ Module.finrank ℝ E) :
    interior K.space = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨s, hs, hscard, _⟩ := K.exists_full_face_of_mem_interior hK hx
  have hle := hcard s hs
  omega

omit [FiniteDimensional ℝ E] in

theorem exists_frontier_notMem_closedStar
    (K : SimplicialComplex ℝ E) (hint : interior K.space = ∅)
    (hzeroK : (0 : E) ∈ K.space) {C : Set E}
    (hC : IsCompact C) (hcv : Convex ℝ C) (hzero : (0 : E) ∈ interior C) :
    ∃ p : frontier C, (p : E) ∉ (K.closedStar 0).space := by
  have hnot : ¬ interior C ⊆ K.space := by
    intro hs
    have hsub : interior C ⊆ interior K.space :=
      interior_maximal hs isOpen_interior
    exact Set.notMem_empty 0 (hint ▸ hsub hzero)
  obtain ⟨x, hxC, hxK⟩ := Set.not_subset.mp hnot
  have hx0 : x ≠ 0 := fun he => hxK (he.symm ▸ hzeroK)
  obtain ⟨p, hp, r, hr, hxp⟩ :=
    hC.exists_frontier_pos_smul hcv hzero (interior_subset hxC) hx0
  refine ⟨⟨p, hp⟩, fun hpstar => hxK ?_⟩
  rw [hxp]
  exact space_subset_of_le (show K.closedStar 0 ≤ K from fun _ hs => hs.1)
    (K.smul_mem_closedStar_zero hpstar ⟨hr.1.le, hr.2⟩)

end Geometry.SimplicialComplex
