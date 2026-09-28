import PoincareConjecture.Proofs.M10.FixedChartHessian
import PoincareConjecture.Proofs.M10.PullbackJacobian
import PoincareConjecture.Proofs.M10.MetricInverse
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial









set_option autoImplicit false

open Set Filter Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricForm_apply (g : RiemannianMetric n M) (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (v w : EuclideanSpace ℝ (Fin n)) :
    pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm y v w =
      g.inner ((extChartAt (𝓡 n) q₀).symm y)
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) v
          ((extChartAt (𝓡 n) q₀).symm y))
        (FiberBundle.extend (EuclideanSpace ℝ (Fin n)) (E := TangentSpace (𝓡 n)) (x := q₀) w
          ((extChartAt (𝓡 n) q₀).symm y)) := by
  have hq : (extChartAt (𝓡 n) q₀).symm y ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [extChartAt_source] using (extChartAt (𝓡 n) q₀).map_target hy
  rw [preferredField_eq_inverseChartDerivative q₀ v hq,
    preferredField_eq_inverseChartDerivative q₀ w hq,
    (extChartAt (𝓡 n) q₀).right_inv hy]
  rfl

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricForm_contDiffOn (g : RiemannianMetric n M) (q₀ : M) :
    ContDiffOn ℝ ∞ (pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm)
      (extChartAt (𝓡 n) q₀).target := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w y hy
  let e := extChartAt (𝓡 n) q₀
  have hq : e.symm y ∈ (chartAt (EuclideanSpace ℝ (Fin n)) q₀).source := by
    simpa only [e, extChartAt_source] using e.map_target hy
  have hp := (preferredField_contMDiffAt_of_mem q₀ v hq).inner_bundle
    (preferredField_contMDiffAt_of_mem q₀ w hq)
  have hi : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e.symm y :=
    (contMDiffOn_extChartAt_symm q₀).contMDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)
  have hc := (hp.comp y hi).contDiffAt
  apply ContDiffAt.contDiffWithinAt
  apply hc.congr_of_eventuallyEq
  filter_upwards [(isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy] with z hz
  exact chartMetricForm_apply g q₀ hz v w

set_option backward.isDefEq.respectTransparency false in

theorem inverseChart_mfderiv_isInvertible (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target) :
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q₀).symm y).IsInvertible := by
  simpa only [modelWithCornersSelf_coe, range_id, mfderivWithin_univ] using
    isInvertible_mfderivWithin_extChartAt_symm (I := 𝓡 n) hy

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricForm_pos (g : RiemannianMetric n M) (q₀ : M)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ≠ 0) :
    0 < pullbackMetricForm g (extChartAt (𝓡 n) q₀).symm y v v := by
  obtain ⟨L, hL⟩ := inverseChart_mfderiv_isInvertible q₀ hy
  apply g.pos
  rw [← hL]
  change L v ≠ 0
  simpa only [map_zero] using L.injective.ne hv

end PoincareConjecture.M10
