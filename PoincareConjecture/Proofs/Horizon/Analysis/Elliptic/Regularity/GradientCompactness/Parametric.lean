import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.Coercivity
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.DominatedConvergence








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology NNReal

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem aestronglyMeasurable_integral_partial_sub_sq_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    {u v : E × ℝ → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u (O ×ˢ I)) (hv : LipschitzOnWith L v (O ×ˢ I))
    (i : Fin d) :
    AEStronglyMeasurable (fun t => ∫ x in U,
      (fderiv ℝ (fun y => u (y, t)) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)) ^ 2)
      (volume.restrict I) := by
  obtain ⟨ue, hue, hueq⟩ := hu.extend_real
  obtain ⟨ve, hve, hveq⟩ := hv.extend_real
  have hum := measurable_fderiv_apply_const_with_param ℝ
    (f := fun t x => ue (x, t)) (hue.continuous.comp continuous_swap)
    (EuclideanSpace.single i 1)
  have hvm := measurable_fderiv_apply_const_with_param ℝ
    (f := fun t x => ve (x, t)) (hve.continuous.comp continuous_swap)
    (EuclideanSpace.single i 1)
  have hmeas := ((hum.sub hvm).pow_const 2).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict U)
  apply hmeas.aestronglyMeasurable.congr
  filter_upwards [ae_restrict_mem hI] with t ht
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem hU] with x hx
  have hueq' : (fun y => u (y, t)) =ᶠ[𝓝 x] fun y => ue (y, t) := by
    filter_upwards [hO.mem_nhds (hUO hx)] with y hy
    exact hueq ⟨hy, ht⟩
  have hveq' : (fun y => v (y, t)) =ᶠ[𝓝 x] fun y => ve (y, t) := by
    filter_upwards [hO.mem_nhds (hUO hx)] with y hy
    exact hveq ⟨hy, ht⟩
  rw [hueq'.fderiv_eq, hveq'.fderiv_eq]
  rfl

theorem norm_integral_partial_sub_sq_le_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    [IsFiniteMeasure (volume.restrict U)]
    {u v : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (hv : LipschitzOnWith L v O) (i : Fin d) :
    ‖∫ x in U, (fderiv ℝ u x (EuclideanSpace.single i 1) -
      fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2‖ ≤
        4 * (L : ℝ) ^ 2 * volume.real U := by
  have hb : ∀ᵐ x ∂volume.restrict U,
      ‖(fderiv ℝ u x (EuclideanSpace.single i 1) -
        fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2‖ ≤ 4 * (L : ℝ) ^ 2 := by
    filter_upwards [ae_restrict_mem hU] with x hx
    have hu' := abs_partial_le_of_lipschitzOn hO hu (hUO hx) i
    have hv' := abs_partial_le_of_lipschitzOn hO hv (hUO hx) i
    have hdiff := (abs_sub _ _).trans (add_le_add hu' hv')
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [mul_self_le_mul_self (abs_nonneg _) hdiff, sq_abs
        (fderiv ℝ u x (EuclideanSpace.single i 1) -
          fderiv ℝ v x (EuclideanSpace.single i 1))]
  simpa only [Measure.real, Measure.restrict_apply_univ] using
    norm_integral_le_of_norm_le_const hb

theorem tendsto_iterated_integral_partial_sub_sq_of_lipschitz
    {O U : Set E} (hO : IsOpen O) (hU : MeasurableSet U) (hUO : U ⊆ O)
    {I : Set ℝ} (hI : MeasurableSet I)
    [IsFiniteMeasure (volume.restrict U)] [IsFiniteMeasure (volume.restrict I)]
    {u : ℕ → E × ℝ → ℝ} {v : E × ℝ → ℝ} {L : ℝ≥0}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) (O ×ˢ I))
    (hv : LipschitzOnWith L v (O ×ˢ I)) (i : Fin d)
    (hlim : ∀ t ∈ I, Tendsto (fun k => ∫ x in U,
      (fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ t in I, ∫ x in U,
      (fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)) ^ 2) atTop (𝓝 0) := by
  have hmeas := hu.mono fun k hk =>
    aestronglyMeasurable_integral_partial_sub_sq_of_lipschitz hO hU hUO hI hk hv i
  have hbound : ∀ᶠ k in atTop, ∀ᵐ t ∂volume.restrict I,
      ‖∫ x in U, (fderiv ℝ (fun y => u k (y, t)) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => v (y, t)) x (EuclideanSpace.single i 1)) ^ 2‖ ≤
          4 * (L : ℝ) ^ 2 * volume.real U := by
    filter_upwards [hu] with k hk
    filter_upwards [ae_restrict_mem hI] with t ht
    have hul : LipschitzOnWith L (fun y => u k (y, t)) O := by
      simpa only [mul_one, Function.comp_def] using hk.comp
        (LipschitzWith.prodMk_right t).lipschitzOnWith (fun y hy => ⟨hy, ht⟩)
    have hvl : LipschitzOnWith L (fun y => v (y, t)) O := by
      simpa only [mul_one, Function.comp_def] using hv.comp
        (LipschitzWith.prodMk_right t).lipschitzOnWith (fun y hy => ⟨hy, ht⟩)
    exact norm_integral_partial_sub_sq_le_of_lipschitz hO hU hUO hul hvl i
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : ℝ => 4 * (L : ℝ) ^ 2 * volume.real U) hmeas hbound
    (integrable_const _) (by
      filter_upwards [ae_restrict_mem hI] with t ht
      exact hlim t ht)
  simpa only [integral_zero] using h

end Poincare.Analysis.Elliptic
