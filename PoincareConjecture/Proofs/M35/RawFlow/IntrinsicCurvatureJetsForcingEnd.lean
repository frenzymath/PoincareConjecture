import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcing
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsForcingDecay
import PoincareConjecture.Proofs.M35.RadialGauge.ForcingSpatialDerivative

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M35.Uniqueness

open SmoothRadial RadialGauge

variable (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
  (H : StandardCapEstimate g₀) (G : PartialStandardCapFlow g₀)
  (hrotation : ∀ t ∈ Ico 0 G.lifetime,
    ∀ A : Matrix.specialOrthogonalGroup (Fin 3) ℝ, ∀ x u v : StandardCapSpace,
      (G.flow.metric t).inner (standardRotation A x)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x u)
        (mfderiv (𝓡 3) (𝓡 3) (standardRotation A) x v) = (G.flow.metric t).inner x u v)
  {T : ℝ} (hT : 0 < T) (hTlt : T < G.lifetime)

local notation "V" => EuclideanSpace ℝ (Fin 5)
local notation "f" => rawWarpingRadius P G hrotation
local notation "v" => rawRadialVelocity P G hrotation
local notation "F" => fun t₀ t (x : V) sigma => smoothGaugeForcing
  (fun r => Real.log (axisDivision (f t) r)) (f t₀) (axisDivision (v t)) x sigma

include hTlt in

theorem raw_intrinsic_gauge_forcing_radial_eq {t t₀ : ℝ}
    (ht : t ∈ Icc 0 T) (ht₀ : t₀ ∈ Icc 0 T) {x : V} (hx : x ≠ 0) (sigma : ℝ) :
    F t₀ t x sigma = radialGaugeForcing (f t) (f t₀) (v t) sigma ‖x‖ ∧
      ‖forcingSpaceDeriv (F t₀ t) x sigma‖ =
        |deriv (radialGaugeForcing (f t) (f t₀) (v t) sigma) ‖x‖| := by
  let h (r : ℝ) := Real.log (axisDivision (f t) r)
  let xi := axisDivision (v t)
  have htG : t ∈ Ico 0 G.lifetime := ⟨ht.1, ht.2.trans_lt hTlt⟩
  have ht₀G : t₀ ∈ Ico 0 G.lifetime := ⟨ht₀.1, ht₀.2.trans_lt hTlt⟩
  have hhe : h = intrinsicLogWarping (G.flow.metric t)
      (hrotation t htG) (G.complete P htG) := by
    dsimp only [h]
    rw [rawWarpingRadius_eq P G hrotation htG]
    rfl
  have hhs : ContDiff ℝ ∞ h := by
    rw [hhe]
    exact intrinsicLogWarping_contDiff _ _ _
  have hhp : Function.Even h := by
    rw [hhe]
    exact intrinsicLogWarping_even _ _ _
  have hhz : h 0 = 0 := by rw [hhe, intrinsicLogWarping_zero]
  have hfs : ContDiff ℝ ∞ (f t₀) := by
    rw [rawWarpingRadius_eq P G hrotation ht₀G]
    exact intrinsicWarpingRadius_contDiff _ _ _
  have hfo : Function.Odd (f t₀) := by
    rw [rawWarpingRadius_eq P G hrotation ht₀G]
    exact intrinsicWarpingRadius_odd _ _ _
  have hfzero : f t₀ 0 = 0 := by
    rw [rawWarpingRadius_eq P G hrotation ht₀G, intrinsicWarpingRadius_zero]
  have hdfzero : deriv (f t₀) 0 = 1 := by
    rw [rawWarpingRadius_eq P G hrotation ht₀G]
    exact (intrinsicWarpingRadius_hasDerivAt_zero _ _ _).deriv
  have hvs : ContDiff ℝ ∞ (v t) := by
    rw [rawRadialVelocity_eq P G hrotation htG]
    exact intrinsicRadialVelocity_contDiff _ _ _
  have hvo : Function.Odd (v t) := by
    rw [rawRadialVelocity_eq P G hrotation htG]
    exact intrinsicRadialVelocity_odd _ _ _
  have hvis : ContDiff ℝ ∞ xi := axisDivision_contDiff hvs
  have hvie : Function.Even xi := axisDivision_even_of_odd hvs hvo
  have hmap : mapRadius h = f t := by
    rw [hhe, rawWarpingRadius_eq P G hrotation htG]
    exact funext (fun r => (intrinsicWarpingRadius_eq_exp _ _ _ r).symm)
  have hvelocity : (fun r => r * xi r) = v t := by
    funext r
    have hz : v t 0 = 0 := by
      rw [rawRadialVelocity_eq P G hrotation htG, intrinsicRadialVelocity_zero]
    simpa only [xi, hz, sub_zero] using mul_axisDivision hvs r
  have heq := smoothGaugeForcing_eq_norm_radial (xi := xi)
    hhs hhp hhz hfs hfo hfzero hdfzero hx sigma
  have hgrad := smoothGaugeForcing_space_norm_eq_radial hhs hhp hhz hfs hfo hfzero hdfzero
    hvis hvie hx sigma
  rw [hmap, hvelocity] at heq hgrad
  exact ⟨heq, hgrad⟩

include H hT hTlt

theorem raw_intrinsic_gauge_forcing_weighted_bound {t₀ : ℝ} (ht₀ : t₀ ∈ Icc 0 T) :
    ∃ C : ℝ, 0 < C ∧ ∀ t ∈ Icc 0 T, ∀ x : V,
      (1 + ‖x‖) * |F t₀ t x 0| ≤ C := by
  obtain ⟨C, hC, hCb⟩ := raw_intrinsic_gauge_forcing_weighted_jets_bounded
    P H G hrotation hT hTlt ht₀ (le_refl (0 : ℝ)) 0
  refine ⟨C + 1, by positivity, ?_⟩
  intro t ht x
  have hv : (1 + ‖x‖) * |F t₀ t x 0| ≤ C := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] using
      hCb t ht x 0 (by norm_num)
  exact hv.trans (le_add_of_nonneg_right zero_le_one)

theorem raw_intrinsic_gauge_forcing_space_vanishes {eta t₀ : ℝ}
    (ht₀ : t₀ ∈ Icc 0 T) :
    ∀ epsilon > 0, ∃ R : ℝ, ∀ t ∈ Icc 0 T, ∀ x : V, ∀ sigma,
      R ≤ ‖x‖ → |sigma| ≤ eta →
      (1 + ‖x‖) * ‖forcingSpaceDeriv (F t₀ t) x sigma‖ < epsilon := by
  obtain ⟨C, hC, hCb⟩ := raw_intrinsic_forcing_weighted_radial_derivative
    P H G hrotation hT hTlt (eta := eta)
  intro epsilon hepsilon
  refine ⟨max (max 1 (Real.exp eta)) (C / epsilon + 1), ?_⟩
  intro t ht x sigma hx hsigma
  have hr : max 1 (Real.exp eta) ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hr1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hr
  have hrp : 0 < ‖x‖ := lt_of_lt_of_le zero_lt_one hr1
  have hx0 : x ≠ 0 := norm_pos_iff.mp hrp
  rw [(raw_intrinsic_gauge_forcing_radial_eq P G hrotation hTlt ht ht₀ hx0 sigma).2]
  apply (hCb t ht t₀ ht₀ ‖x‖ sigma hr hsigma).trans_lt
  apply (div_lt_iff₀ hrp).mpr
  have hR : C / epsilon + 1 ≤ ‖x‖ := (le_max_right _ _).trans hx
  have hdiv : C / epsilon < ‖x‖ := by linarith only [hR]
  simpa only [mul_comm] using (div_lt_iff₀ hepsilon).mp hdiv

end PoincareConjecture.M35.Uniqueness
