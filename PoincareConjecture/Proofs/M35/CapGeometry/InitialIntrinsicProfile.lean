import PoincareConjecture.Proofs.M35.CapGeometry.InitialIntrinsicEscape
import PoincareConjecture.Proofs.M35.RawFlow.IntrinsicCurvatureJetsDecay










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35.Uniqueness



theorem initial_intrinsic_positive_jets_tendsto_zero
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta)
    (hslim : Tendsto s atTop atTop) (j : ℕ) :
    Tendsto (fun k => iteratedDeriv (j + 1)
      (rawWarpingRadius P E.flow.base E.rotation_invariant (t k)) (s k)) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := raw_intrinsic_warping_jets_polynomial_decay
    P E.initial_estimate E.flow.base E.rotation_invariant htheta hthetalt j 1
  have hlimit : Tendsto (fun k => C / s k) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hslim).const_mul C
  apply squeeze_zero_norm' _ hlimit
  filter_upwards [hslim.eventually_ge_atTop 1] with k hk
  have hspos : 0 < s k := zero_lt_one.trans_le hk
  rw [Real.norm_eq_abs]
  apply (le_div_iff₀ hspos).mpr
  have h := hbound (t k) (ht k) (s k) hspos.le
  simp only [pow_one] at h
  have hw : s k ≤ 1 + s k ^ 2 := by nlinarith only [sq_nonneg (s k - 1)]
  have hm := mul_le_mul_of_nonneg_right hw
    (abs_nonneg (iteratedDeriv (j + 1)
      (rawWarpingRadius P E.flow.base E.rotation_invariant (t k)) (s k)))
  simpa only [mul_comm] using hm.trans h




theorem initial_intrinsic_squared_radius_tendsto
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime)
    (t s : ℕ → ℝ) (ht : ∀ k, t k ∈ Icc 0 theta) (hs : ∀ k, 0 < s k)
    {t₀ : ℝ} (ht₀ : t₀ < 1) (htlim : Tendsto t atTop (𝓝 t₀))
    (hslim : Tendsto s atTop atTop) :
    Tendsto (fun k => rawWarpingRadius P E.flow.base E.rotation_invariant (t k) (s k) ^ 2)
      atTop (𝓝 (2 * (1 - t₀))) := by
  let f k := rawWarpingRadius P E.flow.base E.rotation_invariant (t k)
  let S k := (E.flow.connection (t k)).scalarCurvature
    (rawInverseRadius P E.flow.base E.rotation_invariant (t k) (s k) •
      EuclideanSpace.single (2 : Fin 3) 1)
  have htG (k : ℕ) : t k ∈ Ico 0 E.flow.base.lifetime :=
    ⟨(ht k).1, (ht k).2.trans_lt hthetalt⟩
  have hcontrols (k : ℕ) := raw_intrinsic_warping_controls P E.initial_estimate E.flow.base
    (htG k) (E.rotation_invariant (t k) (htG k)) (s k) (hs k)
  have hfpos (k : ℕ) : 0 < f k (s k) := by
    simpa only [f, rawWarpingRadius_eq P E.flow.base E.rotation_invariant (htG k)] using
      (hcontrols k).1
  have hfsq (k : ℕ) : f k (s k) ^ 2 ≤ 2 * E.initial_estimate.scalar_constant := by
    simpa only [f, rawWarpingRadius_eq P E.flow.base E.rotation_invariant (htG k)] using
      (hcontrols k).2.1
  let B := 2 * E.initial_estimate.scalar_constant + 1
  have hH := E.initial_estimate.scalar_constant_pos
  have hfbound (k : ℕ) : |f k (s k)| ≤ B := by
    rw [abs_of_pos (hfpos k)]
    dsimp only [B]
    nlinarith only [hfsq k, sq_nonneg (f k (s k) - 1), hH]
  have hp : Tendsto (fun k => deriv (f k) (s k)) atTop (𝓝 0) := by
    simpa only [f, zero_add, iteratedDeriv_one] using
      initial_intrinsic_positive_jets_tendsto_zero P E htheta hthetalt t s ht hslim 0
  have hpp : Tendsto (fun k => deriv (deriv (f k)) (s k)) atTop (𝓝 0) := by
    simpa only [f, iteratedDeriv_succ', iteratedDeriv_zero] using
      initial_intrinsic_positive_jets_tendsto_zero P E htheta hthetalt t s ht hslim 1
  have hff : Tendsto (fun k => f k (s k) * deriv (deriv (f k)) (s k)) atTop (𝓝 0) := by
    apply squeeze_zero_norm
      (fun k => ?_) (by simpa only [abs_zero, mul_zero] using hpp.abs.const_mul B)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hfbound k) (abs_nonneg _)
  have hformula (k : ℕ) : S k * f k (s k) ^ 2 =
      2 * (1 - deriv (f k) (s k) ^ 2) -
        4 * (f k (s k) * deriv (deriv (f k)) (s k)) := by
    have hh := rotational_scalar_eq_intrinsicWarping (E.flow.metric (t k))
      (E.rotation_invariant (t k) (htG k)) (E.flow.base.complete P (htG k))
      (E.flow.connection (t k)) (hs k)
    have hfeq : intrinsicWarpingRadius (E.flow.metric (t k))
        (E.rotation_invariant (t k) (htG k)) (E.flow.base.complete P (htG k)) = f k := by
      convert! (rawWarpingRadius_eq P E.flow.base E.rotation_invariant (htG k)).symm using 1
    have hreq : (radialArclengthOrderIso (E.flow.metric (t k))
        (E.rotation_invariant (t k) (htG k)) (E.flow.base.complete P (htG k))).symm (s k) =
          rawInverseRadius P E.flow.base E.rotation_invariant (t k) (s k) := by
      convert! (rawInverseRadius_eq P E.flow.base E.rotation_invariant (htG k) (s k)).symm
        using 1
    rw [hfeq, hreq] at hh
    change S k = 2 * (1 - deriv (f k) (s k) ^ 2) / f k (s k) ^ 2 -
      4 * deriv (deriv (f k)) (s k) / f k (s k) at hh
    field_simp [(hfpos k).ne'] at hh
    nlinarith only [hh]
  have hproduct : Tendsto (fun k => S k * f k (s k) ^ 2) atTop (𝓝 2) := by
    have hh := (((tendsto_const_nhds (x := (1 : ℝ))).sub (hp.pow 2)).const_mul 2).sub
      (hff.const_mul 4)
    simp only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero, mul_one, mul_zero] at hh
    simpa only [hformula] using hh
  have hscalar : Tendsto S atTop (𝓝 (1 / (1 - t₀))) :=
    initial_intrinsic_axis_scalar_tendsto P E ⟨htheta.le, hthetalt⟩ t s ht ht₀ htlim hslim
  have hdiv := hproduct.div hscalar (one_div_ne_zero (sub_pos.mpr ht₀).ne')
  have hmodel : 2 / (1 / (1 - t₀)) = 2 * (1 - t₀) := by field_simp
  rw [hmodel] at hdiv
  apply hdiv.congr'
  apply Eventually.of_forall
  intro k
  exact mul_div_cancel_left₀ (f k (s k) ^ 2) (E.scalar_pos (htG k) _).ne'



theorem exists_initial_intrinsic_squared_radius_control
    (P : RicciFlowCurvatureTheory.{0}) {g₀ : StandardInitialMetric}
    (E : RepairedStandardCapExistenceData g₀) {theta eta : ℝ}
    (htheta : 0 < theta) (hthetalt : theta < E.flow.base.lifetime) (heta : 0 < eta) :
    ∃ R : ℝ, 0 < R ∧ ∀ t ∈ Icc 0 theta, ∀ s ≥ R,
      |rawWarpingRadius P E.flow.base E.rotation_invariant t s ^ 2 - 2 * (1 - t)| < eta := by
  classical
  by_contra h
  push Not at h
  choose t ht s hs hbad using fun n : ℕ => h ((n : ℝ) + 1) (by positivity)
  have hslim : Tendsto s atTop atTop := by
    refine tendsto_atTop.2 fun B => ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop B] with k hk
    linarith only [hs k, hk]
  have hspos (k : ℕ) : 0 < s k := (by positivity : 0 < (k : ℝ) + 1).trans_le (hs k)
  obtain ⟨t₀, ht₀, phi, hphi, htlim⟩ := isCompact_Icc.tendsto_subseq ht
  have ht₀one : t₀ < 1 := ht₀.2.trans_lt (E.lifetime_one ▸ hthetalt)
  have hvalue := initial_intrinsic_squared_radius_tendsto P E htheta hthetalt
    (t ∘ phi) (s ∘ phi) (fun k => ht (phi k)) (fun k => hspos (phi k)) ht₀one htlim
    (hslim.comp hphi.tendsto_atTop)
  have herror : Tendsto (fun k => |rawWarpingRadius P E.flow.base E.rotation_invariant
      (t (phi k)) (s (phi k)) ^ 2 - 2 * (1 - t (phi k))|) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, sub_self, abs_zero] using
      (hvalue.sub (((tendsto_const_nhds (x := (1 : ℝ))).sub htlim).const_mul 2)).abs
  obtain ⟨k, hk⟩ := (herror.eventually (eventually_lt_nhds heta)).exists
  exact (not_lt_of_ge (hbad (phi k))) hk

end PoincareConjecture.M35.Uniqueness
