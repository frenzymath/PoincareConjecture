import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.WeakDerivative.LipschitzGreen
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.MeasureTheory.Integral.DominatedConvergence



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped ContDiff Topology NNReal ENNReal

namespace Poincare.Analysis.Elliptic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem memLp_top_directional_fderiv_of_lipschitzOn
    {U : Set E} (hU : IsOpen U) {u : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u U) (w : E) :
    MemLp (fun x => fderiv ℝ u x w) ∞ (μ.restrict U) := by
  obtain ⟨v, hv, heq⟩ := hu.extend_real
  refine (memLp_congr_ae ?_).mp (hv.memLp_lineDeriv (μ := μ.restrict U) w)
  filter_upwards [ae_restrict_mem hU.measurableSet,
    ae_restrict_of_ae (hv.ae_differentiableAt (μ := μ))] with x hx hdx
  have hnear : u =ᶠ[𝓝 x] v := heq.eventuallyEq_of_mem (hU.mem_nhds hx)
  rw [hdx.lineDeriv_eq_fderiv, hnear.fderiv_eq]

theorem setIntegral_mul_fderiv_eq_neg_of_lipschitzOn
    {U : Set E} (hU : IsOpen U) {u φ : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u U) (hφ : ContDiff ℝ ∞ φ)
    (hφc : HasCompactSupport φ) (hφU : tsupport φ ⊆ U) (w : E) :
    (∫ x in U, u x * fderiv ℝ φ x w ∂μ) =
      -(∫ x in U, fderiv ℝ u x w * φ x ∂μ) := by
  have h := WeakDerivative.integral_mul_fderiv_eq_neg μ hU hu hφ hφc hφU w
  have hleft : (∫ x in U, u x * fderiv ℝ φ x w ∂μ) =
      ∫ x, u x * fderiv ℝ φ x w ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport
        (fun h => hx (hφU (tsupport_fderiv_apply_subset ℝ w h))), mul_zero])
  have hright : (∫ x in U, fderiv ℝ u x w * φ x ∂μ) =
      ∫ x, fderiv ℝ u x w * φ x ∂μ :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h)), mul_zero])
  rw [hleft, hright]
  exact h.2.2

theorem ae_directional_fderiv_eq_of_tendsto
    {U : Set E} (hU : IsOpen U) [IsFiniteMeasure (μ.restrict U)]
    {u : ℕ → E → ℝ} {v F : E → ℝ} {L : ℝ≥0} {C : ℝ}
    (hu : ∀ᶠ k in atTop, LipschitzOnWith L (u k) U)
    (hv : LipschitzOnWith L v U)
    (hub : ∀ᶠ k in atTop, ∀ x ∈ U, ‖u k x‖ ≤ C)
    (hlim : ∀ x ∈ U, Tendsto (fun k => u k x) atTop (𝓝 (v x)))
    (w : E) (hF : IntegrableOn F U μ)
    (hdlim : ∀ᵐ x ∂μ.restrict U,
      Tendsto (fun k => fderiv ℝ (u k) x w) atTop (𝓝 (F x))) :
    (fun x => fderiv ℝ v x w) =ᵐ[μ.restrict U] F := by
  have hdv := memLp_top_directional_fderiv_of_lipschitzOn (μ := μ) hU hv w
  have hdvi : IntegrableOn (fun x => fderiv ℝ v x w) U μ := hdv.integrable le_top
  have hzero := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    ((hF.sub hdvi).locallyIntegrableOn) (fun φ hφ hφc hφU => by
      change (∫ x, φ x • (F x - fderiv ℝ v x w) ∂μ) = 0
      have hφi : IntegrableOn φ U μ :=
        (hφ.continuous.integrable_of_hasCompactSupport (μ := μ) hφc).integrableOn
      have hφd : ContDiff ℝ ∞ (fun x => fderiv ℝ φ x w) :=
        (hφ.fderiv_right (by simp)).clm_apply contDiff_const
      have hφdi : IntegrableOn (fun x => fderiv ℝ φ x w) U μ :=
        (hφd.continuous.integrable_of_hasCompactSupport
          (μ := μ) (hφc.fderiv_apply ℝ w)).integrableOn
      have hut : Tendsto (fun k => ∫ x in U, u k x * fderiv ℝ φ x w ∂μ) atTop
          (𝓝 (∫ x in U, v x * fderiv ℝ φ x w ∂μ)) := by
        apply tendsto_integral_filter_of_dominated_convergence
          (fun x => C * ‖fderiv ℝ φ x w‖)
        · exact hu.mono fun k hk =>
            (hk.continuousOn.aestronglyMeasurable hU.measurableSet).mul
              hφd.continuous.aestronglyMeasurable
        · filter_upwards [hub] with k hk
          filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_right (hk x hx) (norm_nonneg _)
        · exact hφdi.norm.const_mul C
        · filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
          exact (hlim x hx).mul_const _
      have hdt : Tendsto (fun k => ∫ x in U, fderiv ℝ (u k) x w * φ x ∂μ) atTop
          (𝓝 (∫ x in U, F x * φ x ∂μ)) := by
        apply tendsto_integral_filter_of_dominated_convergence
          (fun x => (L : ℝ) * ‖w‖ * ‖φ x‖)
        · exact hu.mono fun k hk =>
            (memLp_top_directional_fderiv_of_lipschitzOn (μ := μ) hU hk w).aestronglyMeasurable.mul
              hφ.continuous.aestronglyMeasurable
        · filter_upwards [hu] with k hk
          filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
          rw [norm_mul]
          apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
          exact ((fderiv ℝ (u k) x).le_opNorm w).trans
            (mul_le_mul_of_nonneg_right
              (norm_fderiv_le_of_lipschitzOn ℝ (hU.mem_nhds hx) hk) (norm_nonneg _))
        · exact hφi.norm.const_mul ((L : ℝ) * ‖w‖)
        · exact hdlim.mono fun x hx => hx.mul_const _
      have hid : (∫ x in U, v x * fderiv ℝ φ x w ∂μ) = -(∫ x in U, F x * φ x ∂μ) := by
        apply tendsto_nhds_unique hut
        apply hdt.neg.congr'
        filter_upwards [hu] with k hk
        exact (setIntegral_mul_fderiv_eq_neg_of_lipschitzOn hU hk hφ hφc hφU w).symm
      have hvibp := setIntegral_mul_fderiv_eq_neg_of_lipschitzOn
        (μ := μ) hU hv hφ hφc hφU w
      have hpair : (∫ x in U, F x * φ x ∂μ) = ∫ x in U, fderiv ℝ v x w * φ x ∂μ := by
        linarith
      obtain ⟨D, hD⟩ := hφc.exists_bound_of_continuous hφ.continuous
      have hFφ : IntegrableOn (fun x => F x * φ x) U μ :=
        hF.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
      have hdφ : IntegrableOn (fun x => fderiv ℝ v x w * φ x) U μ :=
        hdvi.mul_bdd hφ.continuous.aestronglyMeasurable (Eventually.of_forall hD)
      have heq : (∫ x in U, φ x • (F x - fderiv ℝ v x w) ∂μ) =
          ∫ x, φ x • (F x - fderiv ℝ v x w) ∂μ :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hφU h)), zero_smul])
      rw [← heq]
      simp_rw [smul_eq_mul, mul_sub, mul_comm (φ _)]
      rw [integral_sub hFφ hdφ, hpair, sub_self])
  filter_upwards [ae_restrict_of_ae hzero, ae_restrict_mem hU.measurableSet] with x hx hxU
  exact (sub_eq_zero.mp (hx hxU)).symm

end Poincare.Analysis.Elliptic
