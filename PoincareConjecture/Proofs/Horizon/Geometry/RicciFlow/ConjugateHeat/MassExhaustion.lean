import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.MetricFamily.Integral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RicciFlow.ConjugateHeat

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ}



theorem continuousOn_cutoffMass
    (F : RicciFlow n M J) {α β : ℝ}
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β))
    {χ : M → ℝ} (hχ : Continuous χ) (hc : HasCompactSupport χ) :
    ContinuousOn (fun τ => ∫ x, u (x, τ) * χ x
      ∂(F.metric (-τ)).volumeMeasure) (Icc α β) := by
  apply F.continuousOn_backward_integral_volumeMeasure_of_compact_support ht hc.isCompact
    (hu.mul (hχ.comp continuous_fst).continuousOn)
  intro τ hτ x hx
  change u (x, τ) * χ x = 0
  rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]



theorem tendsto_integral_weighted_cutoffMass
    (F : RicciFlow n M J) {α β V : ℝ} (hV : 0 ≤ V)
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β))
    (hu0 : ∀ τ ∈ Icc α β, ∀ x, 0 ≤ u (x, τ))
    (hmass : ∀ τ ∈ Icc α β,
      Integrable (fun x => u (x, τ)) (F.metric (-τ)).volumeMeasure ∧
      (∫ x, u (x, τ) ∂(F.metric (-τ)).volumeMeasure) = V)
    (χ : ℕ → M → ℝ) (hχ : ∀ j, Continuous (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hχrange : ∀ j x, χ j x ∈ Icc 0 1)
    (hχlim : ∀ x, Tendsto (fun j => χ j x) atTop (𝓝 1))
    {θ : ℝ → ℝ} (hθ : ContinuousOn θ (Icc α β)) :
    Tendsto (fun j => ∫ τ in Icc α β,
      θ τ * ∫ x, u (x, τ) * χ j x ∂(F.metric (-τ)).volumeMeasure)
      atTop (𝓝 ((∫ τ in Icc α β, θ τ) * V)) := by
  let m := fun j τ => ∫ x, u (x, τ) * χ j x ∂(F.metric (-τ)).volumeMeasure
  have hui (τ : ℝ) (hτ : τ ∈ Icc α β) (j : ℕ) :
      Integrable (fun x => u (x, τ) * χ j x) (F.metric (-τ)).volumeMeasure := by
    apply (hmass τ hτ).1.mono'
      (((hu.comp_continuous (continuous_id.prodMk continuous_const)
        (fun x => ⟨mem_univ x, hτ⟩)).mul (hχ j)).aestronglyMeasurable)
    exact ae_of_all _ (fun x => by
      change ‖u (x, τ) * χ j x‖ ≤ u (x, τ)
      rw [Real.norm_of_nonneg (mul_nonneg (hu0 τ hτ x) (hχrange j x).1)]
      exact mul_le_of_le_one_right (hu0 τ hτ x) (hχrange j x).2)
  have hm (j : ℕ) : ContinuousOn (m j) (Icc α β) :=
    continuousOn_cutoffMass F ht hu (hχ j) (hc j)
  have hmb (j : ℕ) (τ : ℝ) (hτ : τ ∈ Icc α β) : m j τ ∈ Icc 0 V := by
    refine ⟨integral_nonneg (fun x => mul_nonneg (hu0 τ hτ x) (hχrange j x).1), ?_⟩
    rw [← (hmass τ hτ).2]
    exact integral_mono (hui τ hτ j) (hmass τ hτ).1
      (fun x => mul_le_of_le_one_right (hu0 τ hτ x) (hχrange j x).2)
  have hmlim (τ : ℝ) (hτ : τ ∈ Icc α β) :
      Tendsto (fun j => m j τ) atTop (𝓝 V) := by
    rw [← (hmass τ hτ).2]
    apply tendsto_integral_of_dominated_convergence (fun x => u (x, τ))
    · exact fun j => (hui τ hτ j).aestronglyMeasurable
    · exact (hmass τ hτ).1
    · intro j
      exact ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (mul_nonneg (hu0 τ hτ x) (hχrange j x).1)]
        exact mul_le_of_le_one_right (hu0 τ hτ x) (hχrange j x).2)
    · exact ae_of_all _ (fun x => by simpa only [mul_one] using
        (tendsto_const_nhds.mul (hχlim x)))
  have hconv : Tendsto (fun j => ∫ τ in Icc α β, θ τ * m j τ)
      atTop (𝓝 (∫ τ in Icc α β, θ τ * V)) := by
    apply tendsto_integral_of_dominated_convergence (fun τ => |θ τ| * V)
    · exact fun j => (hθ.mul (hm j)).aestronglyMeasurable measurableSet_Icc
    · exact (hθ.abs.mul_const V).integrableOn_Icc
    · intro j
      filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hmb j τ hτ).1]
      exact mul_le_mul_of_nonneg_left (hmb j τ hτ).2 (abs_nonneg _)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with τ hτ
      exact tendsto_const_nhds.mul (hmlim τ hτ)
  simpa only [integral_mul_const] using hconv


theorem tendsto_integral_deriv_cutoffMass
    (F : RicciFlow n M J) {α β V : ℝ} (hαβ : α ≤ β) (hV : 0 ≤ V)
    (ht : ∀ τ ∈ Icc α β, -τ ∈ interior J)
    {u : M × ℝ → ℝ} (hu : ContinuousOn u (univ ×ˢ Icc α β))
    (hu0 : ∀ τ ∈ Icc α β, ∀ x, 0 ≤ u (x, τ))
    (hmass : ∀ τ ∈ Icc α β,
      Integrable (fun x => u (x, τ)) (F.metric (-τ)).volumeMeasure ∧
      (∫ x, u (x, τ) ∂(F.metric (-τ)).volumeMeasure) = V)
    (χ : ℕ → M → ℝ) (hχ : ∀ j, Continuous (χ j))
    (hc : ∀ j, HasCompactSupport (χ j))
    (hχrange : ∀ j x, χ j x ∈ Icc 0 1)
    (hχlim : ∀ x, Tendsto (fun j => χ j x) atTop (𝓝 1))
    {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η) (hs : tsupport η ⊆ Ioo α β) :
    Tendsto (fun j => ∫ τ in Icc α β,
      deriv η τ * ∫ x, u (x, τ) * χ j x ∂(F.metric (-τ)).volumeMeasure)
      atTop (𝓝 0) := by
  have hα : η α = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl α) (hs h).1)
  have hβ : η β = 0 := image_eq_zero_of_notMem_tsupport
    (fun h => (lt_irrefl β) (hs h).2)
  have hi : (∫ τ in Icc α β, deriv η τ) = 0 := by
    rw [← restrict_Ioc_eq_restrict_Icc,
      ← intervalIntegral.integral_of_le hαβ,
      intervalIntegral.integral_deriv_of_contDiffOn_Icc
        (hη.of_le (by simp)).contDiffOn hαβ, hα, hβ, sub_self]
  simpa only [hi, zero_mul] using
    tendsto_integral_weighted_cutoffMass F hV ht hu hu0 hmass χ hχ hc hχrange hχlim
      (hη.deriv' (n := ∞)).continuous.continuousOn

end PoincareConjecture.RicciFlow.ConjugateHeat
