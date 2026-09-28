import PoincareConjecture.Proofs.M10.ChartMetricSmooth

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M10

noncomputable section

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

local instance chartBoundsBilinearNormedAddCommGroup : NormedAddCommGroup
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

local instance chartBoundsBilinearNormedSpace : NormedSpace ℝ
    (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

set_option backward.isDefEq.respectTransparency false in

theorem chartMetricForm_eventually_bounded (g : RiemannianMetric n M) (q₀ : M)
    {C : ℝ} (hC : 0 ≤ C) :
    let e := extChartAt (𝓡 n) q₀
    let B := pullbackMetricForm g e.symm
    ∃ S : ℝ, 1 ≤ S ∧ C ≤ S ∧ ∀ᶠ y in 𝓝 (e q₀),
      y ∈ e.target ∧ ‖B y‖ ≤ S ∧ ‖fderiv ℝ B y‖ ≤ S ∧ ‖(B y).inverse‖ ≤ S := by
  let e := extChartAt (𝓡 n) q₀
  let B := pullbackMetricForm g e.symm
  have htarget : e.target ∈ 𝓝 (e q₀) := extChartAt_target_mem_nhds (I := 𝓡 n) q₀
  have hB : ContDiffAt ℝ ∞ B (e q₀) :=
    (chartMetricForm_contDiffOn g q₀).contDiffAt htarget
  have hi : (B (e q₀)).IsInvertible := positive_bilinear_isInvertible _
    (fun _ hv ↦ chartMetricForm_pos g q₀ (mem_of_mem_nhds htarget) hv)
  let A := fun y ↦ ‖B y‖ + ‖fderiv ℝ B y‖ + ‖(B y).inverse‖
  have hA : ContinuousAt A (e q₀) :=
    (hB.continuousAt.norm.add (hB.continuousAt_fderiv (by simp)).norm).add
      (hi.contDiffAt_map_inverse.comp (e q₀) hB).continuousAt.norm
  have hApos (y : EuclideanSpace ℝ (Fin n)) : 0 ≤ A y := by dsimp only [A]; positivity
  let S := C + A (e q₀) + 1
  have hS : 1 ≤ S := by dsimp only [S]; linarith [hApos (e q₀)]
  have hCS : C ≤ S := by dsimp only [S]; linarith [hApos (e q₀)]
  have hbound : ∀ᶠ y in 𝓝 (e q₀), A y < A (e q₀) + 1 :=
    hA (eventually_lt_nhds (lt_add_one _))
  refine ⟨S, hS, hCS, ?_⟩
  filter_upwards [htarget, hbound] with y hy hAy
  refine ⟨hy, ?_, ?_, ?_⟩ <;>
    dsimp only [A] at hAy <;> dsimp only [S] <;>
    linarith [norm_nonneg (B y), norm_nonneg (fderiv ℝ B y), norm_nonneg ((B y).inverse)]

end

end PoincareConjecture.M10
