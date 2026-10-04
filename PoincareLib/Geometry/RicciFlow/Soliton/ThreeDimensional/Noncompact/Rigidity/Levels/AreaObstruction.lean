import PoincareLib.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.TotalCurvature
import PoincareLib.Geometry.Riemannian.Heat.Energy.VolumeSupport
import PoincareLib.Geometry.Riemannian.Surface.Regularity

/-!
# The compact-surface area obstruction

Gauss--Bonnet fixes total scalar curvature under a change of metric. A metric
with scalar curvature everywhere below one therefore has strictly larger
area than a metric with scalar curvature identically one on the same surface.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareMT.LeviCivitaData

variable {N : Type*} [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N]
  [T3Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N] [CompactSpace N] [Nonempty N]
  {g h : RiemannianMetric 2 N}

/-- Subunit scalar curvature forces strictly more area than a unit-scalar
reference metric on the same compact surface. -/
theorem volume_lt_of_unit_scalar_and_subunit_scalar
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (hunit : ∀ x, D.scalarCurvature x = 1)
    (hsubunit : ∀ x, D'.scalarCurvature x < 1) :
    g.volumeMeasure.real univ < h.volumeMeasure.real univ := by
  let : h.volumeMeasure.IsOpenPosMeasure := h.volumeMeasure_isOpenPosMeasure
  have hc : Continuous (fun x => 1 - D'.scalarCurvature x) :=
    continuous_const.sub D'.continuous_scalarCurvature
  have hi := hc.integrable_of_hasCompactSupport
    (μ := h.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hiR := D'.continuous_scalarCurvature.integrable_of_hasCompactSupport
    (μ := h.volumeMeasure) (HasCompactSupport.of_compactSpace _)
  have hpos := integral_pos_of_integrable_nonneg_nonzero hc hi
    (fun x => (sub_pos.mpr (hsubunit x)).le)
    (ne_of_gt (sub_pos.mpr (hsubunit (Classical.arbitrary N))))
  rw [integral_sub (integrable_const (1 : ℝ)) hiR] at hpos
  have heq := D.integral_scalarCurvature_eq_of_compact_surface D'
  simp only [hunit, integral_const, smul_eq_mul, mul_one] at heq hpos
  linarith

end PoincareMT.LeviCivitaData
