import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.GradientCompactness.LocalL2








noncomputable section
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Topology ENNReal NNReal BigOperators
open Poincare.Analysis.Sobolev.Weak

namespace Poincare.Analysis.Elliptic

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem hasWeakPartialDeriv_fderiv_of_lipschitzOn
    {O : Set E} (hO : IsOpen O) {u : E → ℝ} {L : ℝ≥0}
    (hu : LipschitzOnWith L u O) (i : Fin d) :
    HasWeakPartialDeriv i (fun x => fderiv ℝ u x (EuclideanSpace.single i 1)) u O := by
  obtain ⟨v, hv, heq⟩ := hu.extend_real
  have hae : (fun x => lineDeriv ℝ v x (EuclideanSpace.single i 1)) =ᵐ[volume.restrict O]
      fun x => fderiv ℝ u x (EuclideanSpace.single i 1) := by
    filter_upwards [ae_restrict_mem hO.measurableSet,
      ae_restrict_of_ae (hv.ae_differentiableAt (μ := volume))] with x hx hdx
    have hnear : u =ᶠ[𝓝 x] v := by
      filter_upwards [hO.mem_nhds hx] with y hy
      exact heq hy
    rw [hdx.lineDeriv_eq_fderiv, hnear.fderiv_eq]
  intro φ hφ hc hs
  calc
    (∫ x in O, u x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, v x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
      apply setIntegral_congr_fun hO.measurableSet
      intro x hx
      dsimp only
      rw [heq hx]
    _ = -(∫ x in O, lineDeriv ℝ v x (EuclideanSpace.single i 1) * φ x) :=
      hasWeakPartialDeriv_lineDeriv_of_lipschitz hv i φ hφ hc hs
    _ = -(∫ x in O, fderiv ℝ u x (EuclideanSpace.single i 1) * φ x) := by
      congr 1
      apply integral_congr_ae
      filter_upwards [hae] with x hx
      rw [hx]


theorem lipschitzOnWith_of_tendstoUniformlyOn
    {O : Set E} {u : ℕ → E → ℝ} {v : E → ℝ} {L : ℝ≥0}
    (hu : ∀ k, LipschitzOnWith L (u k) O)
    (hv : TendstoUniformlyOn u v atTop O) : LipschitzOnWith L v O := by
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  exact le_of_tendsto ((hv.tendsto_at hx).dist (hv.tendsto_at hy))
    (Eventually.of_forall fun k => (hu k).dist_le_mul x hx y hy)



theorem tendsto_toLp_of_tendstoUniformlyOn
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {O : Set X}
    (hO : MeasurableSet O) [IsFiniteMeasure (μ.restrict O)]
    {u : ℕ → X → ℝ} {v : X → ℝ}
    (hu : ∀ k, MemLp (u k) 2 (μ.restrict O)) (hv : MemLp v 2 (μ.restrict O))
    (hlim : TendstoUniformlyOn u v atTop O) :
    Tendsto (fun k => (hu k).toLp (u k)) atTop (𝓝 (hv.toLp v)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨a, ha, hsmall⟩ := exists_pos_mul_lt (sq_pos_of_pos hε) (μ.real O + 1)
  let δ := min 1 a
  have hδ : 0 < δ := lt_min (by norm_num) ha
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδa : δ ≤ a := min_le_right _ _
  have hδsq : δ ^ 2 ≤ δ := by nlinarith
  have hbound : δ ^ 2 * μ.real O < ε ^ 2 := by
    calc
      _ ≤ δ * μ.real O := mul_le_mul_of_nonneg_right hδsq (measureReal_nonneg)
      _ ≤ a * (μ.real O + 1) := by gcongr; linarith
      _ < _ := by simpa only [mul_comm] using hsmall
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim δ hδ] with k hk
  have hsquare : Integrable (fun x => (u k x - v x) ^ 2) (μ.restrict O) :=
    (memLp_two_iff_integrable_sq ((hu k).sub hv).aestronglyMeasurable).mp ((hu k).sub hv)
  have hI : (∫ x in O, (u k x - v x) ^ 2 ∂μ) ≤ δ ^ 2 * μ.real O := by
    have h := integral_mono_ae hsquare (integrable_const (δ ^ 2)) ?_
    · simpa only [integral_const, smul_eq_mul, measureReal_restrict_apply_univ,
        mul_comm] using h
    · filter_upwards [ae_restrict_mem hO] with x hx
      have h := hk x hx
      rw [Real.dist_eq, abs_sub_comm] at h
      nlinarith [sq_abs (u k x - v x), abs_nonneg (u k x - v x)]
  rw [dist_eq_norm]
  have hsq := (norm_toLp_sub_sq_eq_integral (hu k) hv).trans_le hI
  have hs := hsq.trans_lt hbound
  nlinarith only [hs, hε, norm_nonneg ((hu k).toLp (u k) - hv.toLp v)]



theorem tendsto_lipschitzPartialL2_of_cauchy
    {O : Set E} (hO : IsOpen O) [IsFiniteMeasure (volume.restrict O)]
    {u : ℕ → E → ℝ} {v : E → ℝ} {L : ℝ≥0}
    (hu : ∀ k, LipschitzOnWith L (u k) O) (hv : LipschitzOnWith L v O)
    (huLp : ∀ k, MemLp (u k) 2 (volume.restrict O)) (hvLp : MemLp v 2 (volume.restrict O))
    (hlim : TendstoUniformlyOn u v atTop O) (i : Fin d)
    (hCauchy : CauchySeq (fun k => lipschitzPartialL2 hO (hu k) i)) :
    Tendsto (fun k => lipschitzPartialL2 hO (hu k) i) atTop
      (𝓝 (lipschitzPartialL2 hO hv i)) := by
  obtain ⟨g, hg⟩ := cauchySeq_tendsto_of_complete hCauchy
  have hfunctions := tendsto_toLp_of_tendstoUniformlyOn hO.measurableSet huLp hvLp hlim
  have hweak : HasWeakPartialDeriv i g v O := by
    have h := weak_partial_of_tendsto_L2 i hfunctions hg ?_
    · intro φ hφ hc hs
      calc
        (∫ x in O, v x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            ∫ x in O, hvLp.toLp v x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
          apply integral_congr_ae
          filter_upwards [hvLp.coeFn_toLp] with x hx
          rw [hx]
        _ = -(∫ x in O, g x * φ x) := h φ hφ hc hs
    · intro k φ hφ hc hs
      calc
        (∫ x in O, (huLp k).toLp (u k) x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
            ∫ x in O, u k x * fderiv ℝ φ x (EuclideanSpace.single i 1) := by
          apply integral_congr_ae
          filter_upwards [(huLp k).coeFn_toLp] with x hx
          rw [hx]
        _ = -(∫ x in O, fderiv ℝ (u k) x (EuclideanSpace.single i 1) * φ x) :=
          hasWeakPartialDeriv_fderiv_of_lipschitzOn hO (hu k) i φ hφ hc hs
        _ = -(∫ x in O, lipschitzPartialL2 hO (hu k) i x * φ x) := by
          congr 1
          apply integral_congr_ae
          filter_upwards [coeFn_lipschitzPartialL2 hO (hu k) i] with x hx
          rw [hx]
  have hactual := hasWeakPartialDeriv_fderiv_of_lipschitzOn hO hv i
  have heq := hweak.ae_eq hO hactual
    ((Lp.memLp g).integrable (by norm_num)).locallyIntegrable
    ((memLp_top_fderiv_apply_of_lipschitzOn hO hv _).integrable le_top).locallyIntegrable
  have hgEq : g = lipschitzPartialL2 hO hv i :=
    Lp.ext (heq.trans (coeFn_lipschitzPartialL2 hO hv i).symm)
  exact hgEq ▸ hg

end Poincare.Analysis.Elliptic
