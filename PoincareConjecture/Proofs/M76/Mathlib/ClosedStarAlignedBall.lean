import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall
import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierAlignedCharts










set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [Nontrivial E] [DecidableEq E]
  {ι : Type*} [Finite ι] [Nonempty ι]





theorem exists_finitePL_closedStar_chart_preserving_halfspaces
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hint : (0 : E) ∈ interior K.space)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    ∃ (C : Set E) (L : (ι ⊕ ι) → E →ₗ[ℝ] ℝ)
      (H : (K.closedStar 0).space ≃ₜ C),
      IsCompact C ∧ Convex ℝ C ∧ (0 : E) ∈ interior C ∧
      (∀ i, L i ≠ 0) ∧ C = {x | ∀ i, L i x ≤ 1} ∧ H.IsFinitePL ∧
      (∀ x : (K.closedStar 0).space,
        (x : E) ∈ (K.link 0).space ↔ (H x : E) ∈ frontier C) ∧
      ∀ A : E →ₗ[ℝ] ℝ, (K.link 0).RespectsAffineHyperplane A.toAffineMap →
        ∀ x : (K.closedStar 0).space,
          (A (H x : E) = 0 ↔ A (x : E) = 0) ∧
          (0 ≤ A (H x : E) ↔ 0 ≤ A (x : E)) := by
  obtain ⟨C, L, _, hC, hcv, hC0, hCU, hdisj, hlocal, hL, hrep, _, _⟩ :=
    K.exists_small_closedStar_halfspace_neighborhood hK hz isOpen_interior hint c
  have hwhole : (K.closedStar 0).space ∩ frontier C = frontier C := by
    apply inter_eq_right.mpr
    intro x hx
    have hxC := hC.isClosed.frontier_subset hx
    exact (hlocal.subset ⟨interior_subset (hCU hxC), hxC⟩).1
  obtain ⟨e, he, heA⟩ := K.exists_finitePL_link_convex_frontier_chart_preserving_halfspaces
    hK hC hcv hC0 hdisj L hL hrep
  let d := e.trans (Homeomorph.setCongr hwhole)
  have hd : d.IsFinitePL := he.setCongr rfl hwhole
  obtain ⟨x, hx⟩ := nonempty_frontier_iff.mpr
    ⟨⟨0, interior_subset hC0⟩, hC.ne_univ⟩
  have hne : (K.link 0).space.Nonempty := ⟨d.symm ⟨x, hx⟩, (d.symm ⟨x, hx⟩).property⟩
  obtain ⟨g, H, hH, hHg, hg0, hbase, hray⟩ :=
    hd.exists_closedStar_extension_radial K hK hz hne hC hcv hC0
  have hsub := space_subset_of_le (K.link_le_closedStar 0)
  have hkeep (y : (K.link 0).space) :
      H ⟨y, hsub y.property⟩ = ⟨d y, hC.isClosed.frontier_subset (d y).property⟩ := by
    apply Subtype.ext
    exact (hHg ⟨y, hsub y.property⟩).trans (hbase y)
  refine ⟨C, L, H, hC, hcv, hC0, hL, hrep, hH,
    H.mem_subset_iff_of_extension d hsub hC.isClosed.frontier_subset hkeep, ?_⟩
  intro A hA y
  by_cases hy0 : (y : E) = 0
  · have hHy : (H y : E) = 0 := (hHg y).trans (by rw [hy0, hg0])
    constructor <;> rw [hHy, hy0]
  · obtain ⟨z, hzlink, r, hr, hyr⟩ := exists_linkPoint_smul y.property hy0
    have hval : (H y : E) = r • (d ⟨z, hzlink⟩ : E) := by
      rw [hHg y, hyr]
      exact hray ⟨z, hzlink⟩ r ⟨hr.1.le, hr.2⟩
    have hmarks := heA A hA ⟨z, hzlink⟩
    change (A (d ⟨z, hzlink⟩ : E) = 0 ↔ A z = 0) ∧
      (0 ≤ A (d ⟨z, hzlink⟩ : E) ↔ 0 ≤ A z) at hmarks
    rw [hval, hyr, map_smul, map_smul]
    simpa only [smul_eq_mul, mul_eq_zero, hr.1.ne', false_or,
      mul_nonneg_iff_of_pos_left hr.1] using hmarks

end Geometry.SimplicialComplex
