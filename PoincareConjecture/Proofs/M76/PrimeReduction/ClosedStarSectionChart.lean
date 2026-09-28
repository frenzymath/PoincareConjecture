import PoincareConjecture.Proofs.M76.PrimeReduction.RadialSectionConeExtension
import PoincareConjecture.Proofs.M76.Mathlib.RadialFrontierAlignedCharts

set_option autoImplicit false

open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {ι : Type*} [Finite ι] [Nonempty ι]

theorem exists_finitePL_closedStar_section_chart
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hz : (0 : E) ∈ K.vertices) (hne : (K.link 0).space.Nonempty)
    {C : Set E} (hC : IsCompact C) (hcv : Convex ℝ C)
    (hC0 : (0 : E) ∈ interior C) (hdisj : Disjoint C (K.link 0).space)
    (L : ι → E →ₗ[ℝ] ℝ) (hL : ∀ i, L i ≠ 0)
    (hrep : C = {x | ∀ i, L i x ≤ 1}) :
    ∃ H : (K.closedStar 0).space ≃ₜ ((K.closedStar 0).space ∩ C : Set E),
      H.IsFinitePL ∧
      (∀ x : (K.closedStar 0).space,
        (x : E) ∈ (K.link 0).space ↔ (H x : E) ∈ frontier C) ∧
      ∀ A : E →ₗ[ℝ] ℝ, (K.link 0).RespectsAffineHyperplane A.toAffineMap →
        ∀ x : (K.closedStar 0).space,
          (A (H x : E) = 0 ↔ A (x : E) = 0) ∧
          (0 ≤ A (H x : E) ↔ 0 ≤ A (x : E)) := by
  obtain ⟨e, he, heA⟩ := K.exists_finitePL_link_convex_frontier_chart_preserving_halfspaces
    hK hC hcv hC0 hdisj L hL hrep
  obtain ⟨g, H, hH, hHg, hg0, hbase, hray⟩ :=
    he.exists_closedStar_section_extension_radial K hK hz hne hC hcv hC0 hdisj
  have hsub := space_subset_of_le (K.link_le_closedStar 0)
  have htarget : (K.closedStar 0).space ∩ frontier C ⊆
      (K.closedStar 0).space ∩ C :=
    fun _ hx => ⟨hx.1, hC.isClosed.frontier_subset hx.2⟩
  have hkeep (x : (K.link 0).space) :
      H ⟨x, hsub x.property⟩ = ⟨e x, htarget (e x).property⟩ := by
    apply Subtype.ext
    exact (hHg ⟨x, hsub x.property⟩).trans (hbase x)
  refine ⟨H, hH, ?_, ?_⟩
  · intro x
    have hb := H.mem_subset_iff_of_extension e hsub htarget hkeep x
    exact hb.trans (and_iff_right (H x).property.1)
  · intro A hA y
    by_cases hy0 : (y : E) = 0
    · have hHy : (H y : E) = 0 := (hHg y).trans (by rw [hy0, hg0])
      constructor <;> rw [hHy, hy0]
    · obtain ⟨z, hzlink, r, hr, hyr⟩ := exists_linkPoint_smul y.property hy0
      have hval : (H y : E) = r • (e ⟨z, hzlink⟩ : E) := by
        rw [hHg y, hyr]
        exact hray ⟨z, hzlink⟩ r ⟨hr.1.le, hr.2⟩
      have hmarks := heA A hA ⟨z, hzlink⟩
      rw [hval, hyr, map_smul, map_smul]
      simpa only [smul_eq_mul, mul_eq_zero, hr.1.ne', false_or,
        mul_nonneg_iff_of_pos_left hr.1] using hmarks

end Geometry.SimplicialComplex
