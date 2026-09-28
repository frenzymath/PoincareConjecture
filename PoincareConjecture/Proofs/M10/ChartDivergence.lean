import PoincareConjecture.Proofs.M10.ChartMetricDual
import PoincareConjecture.Proofs.M10.ChartDensityDerivative
import PoincareConjecture.Proofs.M10.WeightedTrace

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle BigOperators Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in

theorem chart_laplacian_divergence (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {f : M → ℝ} (q₀ : M) {y : EuclideanSpace ℝ (Fin n)}
    (hy : y ∈ (extChartAt (𝓡 n) q₀).target)
    (hf : ContMDiffAt (𝓡 n) (𝓘(ℝ, ℝ)) 2 f ((extChartAt (𝓡 n) q₀).symm y)) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm g e.symm
    let ρ := pullbackJacobian g e.symm
    let a := fun z ↦ (B z).inverse (fderiv ℝ (f ∘ e.symm) z)
    ρ y * D.laplacian f (e.symm y) =
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n))
        (fderiv ℝ (fun z ↦ ρ z • a z) y).toLinearMap := by
  let e := extChartAt (𝓡 n) q₀
  let B := pullbackMetricForm g e.symm
  let ρ := pullbackJacobian g e.symm
  let a := fun z ↦ (B z).inverse (fderiv ℝ (f ∘ e.symm) z)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hB : ContDiffAt ℝ 1 B y :=
    ((chartMetricForm_contDiffOn g q₀).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)).of_le (by simp)
  have hρ : DifferentiableAt ℝ ρ y :=
    ((chartJacobian_contDiffOn g q₀).contDiffAt
      ((isOpen_extChartAt_target (I := 𝓡 n) q₀).mem_nhds hy)).differentiableAt (by simp)
  have hD := inverseChart_mfderiv_isInvertible q₀ hy
  have hDin : Function.Injective (mfderiv (𝓡 n) (𝓡 n) e.symm y) := by
    obtain ⟨L, hL⟩ := hD
    rw [← hL]
    exact L.injective
  obtain ⟨C, hC⟩ := exists_pullback_source_normalization g hD
  have hnorm (v w : EuclideanSpace ℝ (Fin n)) : B y (C v) (C w) = inner ℝ v w := by
    change g.inner (e.symm y)
      (mfderiv (𝓡 n) (𝓡 n) e.symm y (C v))
      (mfderiv (𝓡 n) (𝓡 n) e.symm y (C w)) = _
    rw [hC, hC, metricCoordinates_inner]
  have hi := positive_bilinear_isInvertible (B y)
    (fun _ hv ↦ chartMetricForm_pos g q₀ hy hv)
  have ha : DifferentiableAt ℝ a y :=
    (metricDual_contDiffAt hB (fixedChart_scalar_contDiffAt q₀ hy hf) hi).differentiableAt
      one_ne_zero
  have htrace := trace_eq_sum_normalized_metric b (B y) C hnorm (fderiv ℝ a y).toLinearMap
  have hlap : D.laplacian f (e.symm y) =
      LinearMap.trace ℝ (EuclideanSpace ℝ (Fin n)) (fderiv ℝ a y).toLinearMap +
        (∑ i : Fin n, fderiv ℝ B y (a y) (C (b i)) (C (b i))) / 2 := by
    rw [← sum_metricCoordinates_hessian g D f (e.symm y), htrace]
    rw [Finset.sum_div, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    simpa only [e, B, a, b, ContinuousLinearMap.coe_coe, hC] using
      chartMetricDual_hessian g D q₀ hy hf (C (b i))
  have hdρ := pullbackJacobian_fderiv_eq g hB hDin C hC (a y)
  have hprod := trace_fderiv_smul hρ ha
  dsimp only
  change ρ y * D.laplacian f (e.symm y) = _
  rw [hprod, hlap, hdρ]
  ring

end PoincareConjecture.M10
