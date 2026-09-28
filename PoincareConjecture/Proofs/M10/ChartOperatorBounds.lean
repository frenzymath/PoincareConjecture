import PoincareConjecture.Proofs.M10.ChartMetricBounds
import PoincareConjecture.Proofs.M10.ChartDensitySmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

noncomputable local instance chartOperatorBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

noncomputable local instance chartOperatorBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option backward.isDefEq.respectTransparency false in

theorem chartOperator_eventually_bounded (g : RiemannianMetric n M) (q₀ : M) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm g e.symm
    let ρ := pullbackJacobian g e.symm
    ∃ S : ℝ, 0 ≤ S ∧ ∀ᶠ y in 𝓝 (e q₀), y ∈ e.target ∧
      ‖fderiv ℝ B y‖ ≤ S ∧ ‖(B y).inverse‖ ≤ S ∧ ρ y ≤ S ∧ ‖fderiv ℝ ρ y‖ ≤ S := by
  let e := extChartAt (𝓡 n) q₀
  let ρ := pullbackJacobian g e.symm
  obtain ⟨S, hS, _, hmetric⟩ := chartMetricForm_eventually_bounded g q₀ (C := 0) le_rfl
  have hρ : ContDiffAt ℝ ∞ ρ (e q₀) :=
    (chartJacobian_contDiffOn g q₀).contDiffAt (extChartAt_target_mem_nhds (I := 𝓡 n) q₀)
  let A := fun y ↦ |ρ y| + ‖fderiv ℝ ρ y‖
  have hA : ContinuousAt A (e q₀) :=
    hρ.continuousAt.abs.add (hρ.continuousAt_fderiv (by simp)).norm
  have hnonneg (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ A y := by dsimp only [A]; positivity
  have hbound : ∀ᶠ y in 𝓝 (e q₀), A y < A (e q₀) + 1 :=
    hA (eventually_lt_nhds (lt_add_one _))
  refine ⟨S + A (e q₀) + 1, by linarith [hnonneg (e q₀)], ?_⟩
  filter_upwards [hmetric, hbound] with y hy hyA
  refine ⟨hy.1, ?_, ?_, ?_, ?_⟩
  · linarith [hy.2.2.1, hnonneg (e q₀)]
  · linarith [hy.2.2.2, hnonneg (e q₀)]
  · dsimp only [A] at hyA
    linarith [le_abs_self (ρ y), norm_nonneg (fderiv ℝ ρ y)]
  · dsimp only [A] at hyA
    linarith [abs_nonneg (ρ y)]

end PoincareConjecture.M10
