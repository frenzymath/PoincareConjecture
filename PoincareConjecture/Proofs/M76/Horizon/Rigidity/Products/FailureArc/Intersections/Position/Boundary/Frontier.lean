import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Whole.PairChart
import PoincareConjecture.Proofs.M76.Mathlib.AffineHypersurfaceCharts







set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

local notation "C3" => ((ℝ × ℝ) × ℝ)

theorem OriginalSurfacePairChart.frontier_iff_of_region_halfspace
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {S T R : Set X} {y : X}
    (C : OriginalSurfacePairChart e S T y true)
    (hR : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔
      0 ≤ (C.coordinates z).1.2) :
    ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ frontier R ↔
      (C.coordinates z).1.2 = 0 := by
  let H := C.chart.trans C.coordinates
  let A : C3 →L[ℝ] ℝ :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℝ)
  have hA : A.toContinuousAffineMap.toAffineMap.linear ≠ 0 := by
    intro hh
    have hh' := congrArg (fun L : C3 →ₗ[ℝ] ℝ => L ((0, 1), 0)) hh
    change (1 : ℝ) = 0 at hh'
    exact one_ne_zero hh'
  have hhalf (x : X) (hx : x ∈ H.source) : x ∈ R ↔ 0 ≤ A (H x) := by
    have hh := hR (C.chart x) hx.2
    rwa [C.chart.left_inv hx.1] at hh
  have hfront := H.isImage_frontier_of_affine_nonneg A.toContinuousAffineMap hA hhalf
  intro z hz
  have hzC := C.source_subset hz
  have hx : C.chart.symm z ∈ H.source := by
    refine ⟨C.chart.map_target hzC, ?_⟩
    change C.chart (C.chart.symm z) ∈ C.coordinates.source
    rwa [C.chart.right_inv hzC]
  have hh := (hfront.apply_mem_iff hx).symm
  change C.chart.symm z ∈ frontier R ↔
    (C.coordinates (C.chart (C.chart.symm z))).1.2 = 0 at hh
  simpa only [C.chart.right_inv hzC] using hh

end PoincareConjecture.M76
