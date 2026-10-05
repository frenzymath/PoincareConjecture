import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Metric.Coordinates.ChartMetricSmooth
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Exponential.Jacobian.DeterminantCalculus
import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Metric.Coordinates.MetricCoordinates

/-!
# Smooth genuine Gram density and a frozen orthonormal normalization

Positivity of the actual inverse-chart differential gives a positive
Gram determinant. Smooth determinant and square-root calculus then
apply to the genuine volume density. A source normalization is chosen
once at the evaluation point and kept fixed for differentiation.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Smoothness of the actual pullback form gives smoothness of its positive Gram density. -/
theorem pullbackJacobian_contDiffAt_of_form (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {y : EuclideanSpace ℝ (Fin n)} {k : ℕ∞ω}
    (hB : ContDiffAt ℝ k (pullbackMetricForm g f) y)
    (hD : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f y)) :
    ContDiffAt ℝ k (pullbackJacobian g f) y := by
  let A := fun z ↦ (fun i j : Fin n ↦ pullbackMetricForm g f z
    (EuclideanSpace.basisFun (Fin n) ℝ i) (EuclideanSpace.basisFun (Fin n) ℝ j))
  have hA : ContDiffAt ℝ k A y :=
    contDiffAt_pi.mpr (fun _ ↦ contDiffAt_pi.mpr (fun _ ↦
      (hB.clm_apply contDiffAt_const).clm_apply contDiffAt_const))
  have hdet : ContDiffAt ℝ k (fun z ↦ Matrix.det (A z)) y := by
    have h := (continuousRowDeterminant (ι := Fin n)).contDiff.contDiffAt.comp y hA
    apply h.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall (fun z ↦ (continuousRowDeterminant_apply (A z)).symm)
  have hpos : 0 < Matrix.det (A y) := Real.sqrt_pos.mp (pullbackJacobian_pos g hD)
  exact hdet.sqrt hpos.ne'

set_option backward.isDefEq.respectTransparency false in
/-- The actual inverse-chart Gram density is smooth throughout the chart target. -/
theorem chartJacobian_contDiffOn (g : RiemannianMetric n M) (q₀ : M) :
    ContDiffOn ℝ ∞ (pullbackJacobian g (extChartAt (𝓡 n) q₀).symm)
      (extChartAt (𝓡 n) q₀).target := by
  intro y hy
  apply ContDiffAt.contDiffWithinAt
  apply pullbackJacobian_contDiffAt_of_form g
    ((chartMetricForm_contDiffOn g q₀).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy))
  obtain ⟨L, hL⟩ := inverseChart_mfderiv_isInvertible q₀ hy
  rw [← hL]
  exact L.injective

set_option backward.isDefEq.respectTransparency false in
/-- One fixed source equivalence makes the actual differential orthonormal at the chosen point. -/
theorem exists_pullback_source_normalization (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {y : EuclideanSpace ℝ (Fin n)}
    (hD : (mfderiv (𝓡 n) (𝓡 n) f y).IsInvertible) :
    ∃ C : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n),
      ∀ v, mfderiv (𝓡 n) (𝓡 n) f y (C v) = metricCoordinates g (f y) v := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  obtain ⟨L, hL⟩ := hD
  refine ⟨(metricCoordinates g (f y)).toContinuousLinearEquiv.trans L.symm, ?_⟩
  intro v
  rw [← hL]
  exact L.apply_symm_apply _

end PoincareMT.ReducedVolume
