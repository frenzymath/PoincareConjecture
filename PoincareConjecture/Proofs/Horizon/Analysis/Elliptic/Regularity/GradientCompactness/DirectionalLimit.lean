import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.TimeIdentification

noncomputable section
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal

namespace Poincare.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem ae_directional_fderiv_eq_of_bounded_tendsto
    {U : Set E} (hU : IsOpen U) [IsFiniteMeasure (μ.restrict U)]
    {u : ℕ → E → ℝ} {v F : E → ℝ} {L : ℝ≥0} {C : ℝ}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) U)
    (hv : LipschitzOnWith L v U)
    (hub : ∀ᶠ k in atTop, ∀ x ∈ U, ‖u k x‖ ≤ C)
    (hlim : ∀ x ∈ U, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (w : E)
    (hdlim : ∀ᵐ x ∂μ.restrict U,
      Tendsto (fun k => fderiv ℝ (u k) x w) atTop (𝓝 (F x))) :
    (fun x => fderiv ℝ v x w) =ᵐ[μ.restrict U] F := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hu
  have hm (k : ℕ) : AEStronglyMeasurable
      (fun x => fderiv ℝ (u (k + N)) x w) (μ.restrict U) :=
    (memLp_top_directional_fderiv_of_lipschitzOn (μ := μ) hU
      (hN _ (Nat.le_add_left N k)) w).aestronglyMeasurable
  have hFm : AEStronglyMeasurable F (μ.restrict U) :=
    aestronglyMeasurable_of_tendsto_ae atTop hm
      (hdlim.mono fun x hx => hx.comp (tendsto_add_atTop_nat N))
  have hFb : ∀ᵐ x ∂μ.restrict U, ‖F x‖ ≤ (L : ℝ) * ‖w‖ := by
    filter_upwards [hdlim, ae_restrict_mem hU.measurableSet] with x hx hxU
    apply le_of_tendsto hx.norm
    filter_upwards [hu] with k hk
    exact ((fderiv ℝ (u k) x).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right
        (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hxU) hk) (norm_nonneg _))
  exact ae_directional_fderiv_eq_of_tendsto hU hu hv hub hlim w
    ((memLp_top_of_bound hFm _ hFb).integrable le_top) hdlim

end Poincare.Analysis.Elliptic
