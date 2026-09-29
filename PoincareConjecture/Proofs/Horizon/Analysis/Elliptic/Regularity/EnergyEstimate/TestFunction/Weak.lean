/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Nirenberg/TestFunction/DiffQuotTestFunction.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.Basic
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.Derivatives

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Poincare.Analysis.Sobolev
open scoped ENNReal NNReal Convolution Pointwise BigOperators

namespace Poincare.Analysis.Sobolev.NirenbergDiffQuotTestFunction

variable {d : ℕ} [NeZero d]

local notation "EuclN" => EuclideanSpace ℝ (Fin d)

noncomputable def nirenbergTestFunction
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) : EuclN → ℝ :=
  translate k (-h) (fun x => (η x)^2 * diffQuot k h u x)

omit [NeZero d] in
@[simp] lemma nirenbergTestFunction_apply
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) (x : EuclN) :
    nirenbergTestFunction k h η u x =
      (η (x + (-h) • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) := rfl

omit [NeZero d] in
lemma nirenbergTestFunction_apply_sub
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) (x : EuclN) :
    nirenbergTestFunction k h η u x =
      (η (x - h • EuclideanSpace.single k 1))^2 *
        diffQuot k h u (x - h • EuclideanSpace.single k 1) := by
  simp [nirenbergTestFunction, translate, sub_eq_add_neg, neg_smul]

omit [NeZero d] in
theorem nirenbergTestFunction_support_subset
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) :
    Function.support (nirenbergTestFunction k h η u) ⊆
      {x | x + (-h) • EuclideanSpace.single k 1 ∈ Function.support η} := by
  intro x hx
  change (η (x + (-h) • EuclideanSpace.single k 1))^2 *
      diffQuot k h u (x + (-h) • EuclideanSpace.single k 1) ≠ 0 at hx
  by_contra hxη
  have hη_zero : η (x + (-h) • EuclideanSpace.single k 1) = 0 := by
    by_contra hne
    exact hxη hne
  apply hx
  have hη_sq_zero : (η (x + (-h) • EuclideanSpace.single k 1))^2 = 0 := by
    rw [hη_zero]; ring
  rw [hη_sq_zero, zero_mul]

omit [NeZero d] in
theorem nirenbergTestFunction_tsupport_subset
    (k : Fin d) (h : ℝ) (η u : EuclN → ℝ) :
    tsupport (nirenbergTestFunction k h η u) ⊆
      {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} := by
  have htrans_cont : Continuous
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_closed_pre : IsClosed
      {x : EuclN | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport η} :=
    isClosed_tsupport η |>.preimage htrans_cont
  refine closure_minimal ?_ h_closed_pre
  intro x hx
  exact subset_tsupport η
    (nirenbergTestFunction_support_subset (d := d) k h η u hx)

omit [NeZero d] in
theorem nirenbergTestFunction_hasCompactSupport
    (k : Fin d) (h : ℝ) {η : EuclN → ℝ} (hη_cs : HasCompactSupport η)
    (u : EuclN → ℝ) :
    HasCompactSupport (nirenbergTestFunction k h η u) := by
  set v : EuclN := (-h) • EuclideanSpace.single k 1 with hv_def
  set htrans_homeo : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight v with htrans_def
  have h_sub : tsupport (nirenbergTestFunction k h η u) ⊆
      {x : EuclN | x + v ∈ tsupport η} :=
    nirenbergTestFunction_tsupport_subset (d := d) k h η u
  have h_set_eq :
      {x : EuclN | x + v ∈ tsupport η} = htrans_homeo ⁻¹' (tsupport η) := by
    ext x
    simp [htrans_homeo]
  rw [h_set_eq] at h_sub
  have h_pre_eq :
      htrans_homeo ⁻¹' (tsupport η) = htrans_homeo.symm '' (tsupport η) := by
    ext x
    constructor
    · intro hx
      refine ⟨htrans_homeo x, hx, ?_⟩
      exact htrans_homeo.symm_apply_apply x
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hx
      have : htrans_homeo x = y := by
        rw [← hyx, htrans_homeo.apply_symm_apply]
      rw [Set.mem_preimage, this]
      exact hy
  have h_pre_compact : IsCompact (htrans_homeo ⁻¹' (tsupport η)) := by
    rw [h_pre_eq]
    exact hη_cs.image htrans_homeo.symm.continuous
  exact h_pre_compact.of_isClosed_subset (isClosed_tsupport _) h_sub

omit [NeZero d] in
theorem sq_nirenbergTestFunction_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η) (x : EuclN) :
    (nirenbergTestFunction k h η u x)^2 ≤
      M_η^4 *
        (diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2 := by
  set y : EuclN := x + (-h) • EuclideanSpace.single k 1 with hy_def
  have h_unfold :
      (nirenbergTestFunction k h η u x)^2 =
        ((η y)^2)^2 * (diffQuot k h u y)^2 := by
    rw [nirenbergTestFunction_apply]
    ring
  rw [h_unfold]
  have h_sq_le : (η y)^2 ≤ M_η^2 := by
    have hY := hM_η y
    have h_abs_sq : (η y)^2 = |η y|^2 := by rw [sq_abs]
    rw [h_abs_sq]
    exact pow_le_pow_left₀ (abs_nonneg _) hY 2
  have h_quartic_le : ((η y)^2)^2 ≤ M_η^4 := by
    have : ((η y)^2)^2 ≤ (M_η^2)^2 := by
      have h_sq_nn : 0 ≤ (η y)^2 := sq_nonneg _
      exact pow_le_pow_left₀ h_sq_nn h_sq_le 2
    have hM4 : (M_η^2)^2 = M_η^4 := by ring
    rw [← hM4]; exact this
  have h_dq_sq_nn : 0 ≤ (diffQuot k h u y)^2 := sq_nonneg _
  exact mul_le_mul_of_nonneg_right h_quartic_le h_dq_sq_nn

omit [NeZero d] in
theorem aestronglyMeasurable_nirenbergTestFunction
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    (hη : AEStronglyMeasurable η (volume : Measure EuclN))
    (hu : AEStronglyMeasurable u (volume : Measure EuclN)) :
    AEStronglyMeasurable (nirenbergTestFunction k h η u)
      (volume : Measure EuclN) := by
  have hη_sq : AEStronglyMeasurable (fun y : EuclN => (η y)^2)
      (volume : Measure EuclN) := hη.pow 2
  have hdq : AEStronglyMeasurable (diffQuot k h u) (volume : Measure EuclN) :=
    aestronglyMeasurable_diffQuot (d := d) k h hu
  have hg : AEStronglyMeasurable
      (fun y : EuclN => (η y)^2 * diffQuot k h u y)
      (volume : Measure EuclN) := hη_sq.mul hdq
  have hMP : MeasurePreserving
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) volume volume :=
    measurePreserving_add_right volume _
  exact hg.comp_measurePreserving hMP

omit [NeZero d] in
private lemma lintegral_translate_diffQuot_sq
    (k : Fin d) (h : ℝ) (u : EuclN → ℝ) :
    ∫⁻ x : EuclN,
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
          : ℝ≥0∞) ^ (2 : ℕ) ∂(volume : Measure EuclN) =
      ∫⁻ y : EuclN,
        (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
        ∂(volume : Measure EuclN) := by
  have hMP : MeasurePreserving
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) volume volume :=
    measurePreserving_add_right volume _
  set htrans_homeo : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight ((-h) • EuclideanSpace.single k 1) with htrans_def
  have h_emb : MeasurableEmbedding htrans_homeo :=
    htrans_homeo.measurableEmbedding
  have h_fun_eq : (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) =
      htrans_homeo := by
    funext x
    simp [htrans_homeo]
  have hMP' : MeasurePreserving htrans_homeo volume volume := by
    rw [← h_fun_eq]; exact hMP
  have h_step : ∫⁻ x : EuclN,
        (‖diffQuot k h u (htrans_homeo x)‖ₑ : ℝ≥0∞) ^ (2 : ℕ) =
      ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ) :=
    hMP'.lintegral_comp_emb h_emb
      (fun y : EuclN => (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ))
  have h_congr : (fun x : EuclN =>
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞)
          ^ (2 : ℕ)) =
      (fun x : EuclN =>
        (‖diffQuot k h u (htrans_homeo x)‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) := by
    funext x
    have : x + (-h) • EuclideanSpace.single k 1 = htrans_homeo x := by
      simp [htrans_homeo]
    rw [this]
  rw [h_congr]
  exact h_step

omit [NeZero d] in
theorem eLpNorm_nirenbergTestFunction_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η) :
    eLpNorm (nirenbergTestFunction k h η u) 2 (volume : Measure EuclN) ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ ∞ := by norm_num
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  have h_pow_eq : ∀ a : ℝ≥0∞, a ^ (2 : ℝ) = a ^ (2 : ℕ) := by
    intro a
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  have h_pt_enorm : ∀ x : EuclN,
      (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞)^(2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) *
          (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
            : ℝ≥0∞)^(2 : ℕ) := by
    intro x
    have h_real :=
      sq_nirenbergTestFunction_le (d := d) (u := u) k h hM_η x
    have h_lhs_eq :
        (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal ((nirenbergTestFunction k h η u x)^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    have h_rhs_eq :
        (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ : ℝ≥0∞)^(2 : ℕ) =
          ENNReal.ofReal
            ((diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) := by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]
    rw [h_lhs_eq, h_rhs_eq]
    have hM4_nn : 0 ≤ M_η^4 := by positivity
    rw [show ENNReal.ofReal (M_η^4) *
        ENNReal.ofReal
          ((diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) =
      ENNReal.ofReal (M_η^4 *
        (diffQuot k h u (x + (-h) • EuclideanSpace.single k 1))^2) from
        (ENNReal.ofReal_mul hM4_nn).symm]
    exact ENNReal.ofReal_le_ofReal h_real
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top,
    eLpNorm_eq_lintegral_rpow_enorm_toReal h2_ne_zero h2_ne_top]
  rw [h2_toReal]
  have h_lhs_pow_eq :
      (∫⁻ x : EuclN,
          (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ x : EuclN,
          (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with x using h_pow_eq _
  have h_rhs_pow_eq :
      (∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℝ)
          ∂(volume : Measure EuclN)) =
        ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)
          ∂(volume : Measure EuclN) := by
    refine lintegral_congr_ae ?_
    filter_upwards with y using h_pow_eq _
  rw [h_lhs_pow_eq, h_rhs_pow_eq]
  have h_lint_le :
      ∫⁻ x : EuclN, (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ) ≤
        ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN, (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ) := by
    have h_step :
        ∫⁻ x : EuclN, (‖nirenbergTestFunction k h η u x‖ₑ : ℝ≥0∞) ^ (2 : ℕ) ≤
          ∫⁻ x : EuclN,
            ENNReal.ofReal (M_η^4) *
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) := by
      refine lintegral_mono_ae ?_
      filter_upwards with x using h_pt_enorm x
    have h_const_pull :
        ∫⁻ x : EuclN,
            ENNReal.ofReal (M_η^4) *
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) =
          ENNReal.ofReal (M_η^4) *
            ∫⁻ x : EuclN,
              (‖diffQuot k h u (x + (-h) • EuclideanSpace.single k 1)‖ₑ
                : ℝ≥0∞) ^ (2 : ℕ) := by
      rw [lintegral_const_mul']
      exact ENNReal.ofReal_ne_top
    rw [h_const_pull] at h_step
    rw [lintegral_translate_diffQuot_sq (d := d) k h u] at h_step
    exact h_step
  refine le_trans (ENNReal.rpow_le_rpow h_lint_le (by norm_num : (0 : ℝ) ≤ 1/2)) ?_
  have hM4_nn : 0 ≤ M_η^4 := by positivity
  have h_mul_rpow :
      (ENNReal.ofReal (M_η^4) *
          ∫⁻ y : EuclN,
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) =
        (ENNReal.ofReal (M_η^4)) ^ ((1 : ℝ) / 2) *
          (∫⁻ y : EuclN,
            (‖diffQuot k h u y‖ₑ : ℝ≥0∞) ^ (2 : ℕ)) ^ ((1 : ℝ) / 2) := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1/2)]
  rw [h_mul_rpow]
  have h_sqrt_M4 :
      (ENNReal.ofReal (M_η^4)) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (M_η^2) := by
    have hM2_nn : 0 ≤ M_η^2 := sq_nonneg _
    have h_M4_to_pow :
        ENNReal.ofReal (M_η^4) = (ENNReal.ofReal (M_η^2)) ^ (2 : ℕ) := by
      rw [show M_η^4 = (M_η^2)^(2 : ℕ) from by ring,
        ENNReal.ofReal_pow hM2_nn 2]
    rw [h_M4_to_pow]
    rw [← ENNReal.rpow_natCast (ENNReal.ofReal (M_η^2)) 2,
      ← ENNReal.rpow_mul]
    have h_calc : ((2 : ℕ) : ℝ) * (1 / 2) = 1 := by norm_num
    rw [h_calc, ENNReal.rpow_one]
  rw [h_sqrt_M4]

omit [NeZero d] in
private lemma volume_compact_lt_top {K : Set EuclN} (hK : IsCompact K) :
    (volume : Measure EuclN) K < ∞ := hK.measure_lt_top

omit [NeZero d] in
theorem eLpNorm_nirenbergTestFunction_restrict_le
    (k : Fin d) (h : ℝ) {η u : EuclN → ℝ}
    {M_η : ℝ} (hM_η : ∀ x, |η x| ≤ M_η)
    (Ω' : Set EuclN) :
    eLpNorm (nirenbergTestFunction k h η u) 2 ((volume : Measure EuclN).restrict Ω') ≤
      ENNReal.ofReal (M_η^2) *
        eLpNorm (diffQuot k h u) 2 (volume : Measure EuclN) := by
  refine le_trans ?_ (eLpNorm_nirenbergTestFunction_le (d := d) k h hM_η)
  exact eLpNorm_mono_measure _ Measure.restrict_le_self

omit [NeZero d] in
private lemma tsupport_translate_subset
    (k : Fin d) (h : ℝ) (φ : EuclN → ℝ) :
    tsupport (translate k (-h) φ) ⊆
      {x | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport φ} := by
  have htrans_cont : Continuous
      (fun x : EuclN => x + (-h) • EuclideanSpace.single k 1) :=
    continuous_id.add continuous_const
  have h_closed : IsClosed
      {x : EuclN | x + (-h) • EuclideanSpace.single k 1 ∈ tsupport φ} :=
    isClosed_tsupport φ |>.preimage htrans_cont
  refine closure_minimal ?_ h_closed
  intro x hx
  change φ (x + (-h) • EuclideanSpace.single k 1) ≠ 0 at hx
  exact subset_tsupport φ hx

omit [NeZero d] in
private lemma contDiff_translate (k : Fin d) (h : ℝ) {φ : EuclN → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) : ContDiff ℝ (⊤ : ℕ∞) (translate k h φ) := by
  unfold translate
  have htrans_smooth : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : EuclN => y + h • EuclideanSpace.single k 1) :=
    contDiff_id.add contDiff_const
  exact hφ.comp htrans_smooth

omit [NeZero d] in
private lemma hasCompactSupport_translate (k : Fin d) (h : ℝ) {φ : EuclN → ℝ}
    (hφ_supp : HasCompactSupport φ) :
    HasCompactSupport (translate k h φ) := by
  let φ_homeo : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have h_eq : (translate k h φ) = φ ∘ φ_homeo := by
    funext x; rfl
  rw [h_eq]
  exact hφ_supp.comp_homeomorph φ_homeo

omit [NeZero d] in
private lemma fderiv_translate_apply (k j : Fin d) (h : ℝ) {φ : EuclN → ℝ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : EuclN) :
    (fderiv ℝ (translate k h φ) x) (EuclideanSpace.single j 1) =
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1))
        (EuclideanSpace.single j 1) := by
  have hφ_diff : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hφ_at : HasFDerivAt φ
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1))
      (x + h • EuclideanSpace.single k 1) :=
    (hφ_diff (x + h • EuclideanSpace.single k 1)).hasFDerivAt
  have h_translate_at : HasFDerivAt
      (fun z : EuclN => z + h • EuclideanSpace.single k 1)
      (ContinuousLinearMap.id ℝ EuclN) x :=
    (hasFDerivAt_id x).add_const _
  have h_comp_at : HasFDerivAt
      (fun z : EuclN => φ (z + h • EuclideanSpace.single k 1))
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1)) x := by
    have hcomp := hφ_at.comp x h_translate_at
    have heq :
        ((fderiv ℝ φ (x + h • EuclideanSpace.single k 1)).comp
            (ContinuousLinearMap.id ℝ EuclN)) =
          fderiv ℝ φ (x + h • EuclideanSpace.single k 1) := by
      ext z; rfl
    rw [heq] at hcomp
    exact hcomp
  have h_at : HasFDerivAt (translate k h φ)
      (fderiv ℝ φ (x + h • EuclideanSpace.single k 1)) x := h_comp_at
  rw [h_at.fderiv]

omit [NeZero d] in
private lemma tsupport_subset_univ (φ : EuclN → ℝ) :
    tsupport φ ⊆ (Set.univ : Set EuclN) := fun _ _ => trivial

omit [NeZero d] in
theorem hasWeakPartialDeriv_translate
    (k j : Fin d) (h : ℝ) {f g : EuclN → ℝ}
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g f Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (translate k (-h) g) (translate k (-h) f) Set.univ := by
  intro φ hφ_smooth hφ_supp _hφ_sub
  set ψ : EuclN → ℝ := translate k h φ with hψ_def
  have hψ_smooth : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_translate (d := d) k h hφ_smooth
  have hψ_cs : HasCompactSupport ψ :=
    hasCompactSupport_translate (d := d) k h hφ_supp
  have h_test :=
    hwp ψ hψ_smooth hψ_cs (tsupport_subset_univ ψ)
  rw [setIntegral_univ, setIntegral_univ] at h_test
  rw [setIntegral_univ, setIntegral_univ]
  have h_LHS_subst :
      ∫ x, f x * (fderiv ℝ ψ x) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) =
        ∫ z, translate k (-h) f z *
          (fderiv ℝ φ z) (EuclideanSpace.single j 1)
          ∂(volume : Measure EuclN) := by
    have h_int_eq :=
      integral_add_right_eq_self (μ := (volume : Measure EuclN))
        (f := fun x : EuclN =>
          f x * (fderiv ℝ ψ x) (EuclideanSpace.single j 1))
        ((-h) • EuclideanSpace.single k 1)
    rw [← h_int_eq]
    refine integral_congr_ae ?_
    filter_upwards with z
    have h_lhs_unfold : translate k (-h) f z =
        f (z + (-h) • EuclideanSpace.single k 1) := rfl
    rw [h_lhs_unfold]
    have hψ_eq_translate : ψ = translate k h φ := rfl
    rw [hψ_eq_translate]
    have h_apply :
        (fderiv ℝ (translate k h φ) (z + (-h) • EuclideanSpace.single k 1))
            (EuclideanSpace.single j 1) =
          (fderiv ℝ φ
            ((z + (-h) • EuclideanSpace.single k 1) +
              h • EuclideanSpace.single k 1))
            (EuclideanSpace.single j 1) :=
      fderiv_translate_apply (d := d) k j h hφ_smooth
        (z + (-h) • EuclideanSpace.single k 1)
    rw [h_apply]
    have h_cancel :
        (z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1 = z := by
      rw [add_assoc, ← add_smul]
      simp
    rw [h_cancel]
  have h_RHS_subst :
      ∫ x, g x * ψ x ∂(volume : Measure EuclN) =
        ∫ z, translate k (-h) g z * φ z ∂(volume : Measure EuclN) := by
    have h_int_eq :=
      integral_add_right_eq_self (μ := (volume : Measure EuclN))
        (f := fun x : EuclN => g x * ψ x)
        ((-h) • EuclideanSpace.single k 1)
    rw [← h_int_eq]
    refine integral_congr_ae ?_
    filter_upwards with z
    have h_g_unfold : translate k (-h) g z =
        g (z + (-h) • EuclideanSpace.single k 1) := rfl
    rw [h_g_unfold]
    have h_psi_eq : ψ (z + (-h) • EuclideanSpace.single k 1) = φ z := by
      change φ ((z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1) = φ z
      have : (z + (-h) • EuclideanSpace.single k 1) +
            h • EuclideanSpace.single k 1 = z := by
        rw [add_assoc, ← add_smul]
        simp
      rw [this]
    rw [h_psi_eq]
  rw [h_LHS_subst] at h_test
  rw [h_RHS_subst] at h_test
  exact h_test

omit [NeZero d] in
theorem hasWeakPartialDeriv_add_univ
    (j : Fin d) {f₁ f₂ g₁ g₂ : EuclN → ℝ}
    (hf₁_locInt :
      LocallyIntegrable f₁ ((volume : Measure EuclN).restrict Set.univ))
    (hf₂_locInt :
      LocallyIntegrable f₂ ((volume : Measure EuclN).restrict Set.univ))
    (hg₁_locInt :
      LocallyIntegrable g₁ ((volume : Measure EuclN).restrict Set.univ))
    (hg₂_locInt :
      LocallyIntegrable g₂ ((volume : Measure EuclN).restrict Set.univ))
    (h1 : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g₁ f₁ Set.univ)
    (h2 : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g₂ f₂ Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (g₁ + g₂) (f₁ + f₂) Set.univ := by
  intro φ hφ_smooth hφ_supp _hφ_sub
  have hint_partial_φ_locL1 :
      LocallyIntegrable
        (fun x => (fderiv ℝ φ x) (EuclideanSpace.single j 1))
        ((volume : Measure EuclN).restrict Set.univ) := by
    have h_cont : Continuous (fun x : EuclN =>
        (fderiv ℝ φ x) (EuclideanSpace.single j 1)) :=
      (hφ_smooth.continuous_fderiv (by simp)).clm_apply continuous_const
    rw [Measure.restrict_univ]
    exact h_cont.locallyIntegrable
  have hφ_locL1 :
      LocallyIntegrable φ ((volume : Measure EuclN).restrict Set.univ) := by
    rw [Measure.restrict_univ]
    exact hφ_smooth.continuous.locallyIntegrable
  have heq1 := h1 φ hφ_smooth hφ_supp (tsupport_subset_univ φ)
  have heq2 := h2 φ hφ_smooth hφ_supp (tsupport_subset_univ φ)
  rw [setIntegral_univ, setIntegral_univ] at heq1 heq2
  rw [setIntegral_univ, setIntegral_univ]
  have hint_f1_partial : Integrable
      (fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      (volume : Measure EuclN) := by
    have h := (hf₁_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)))
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  have hint_f2_partial : Integrable
      (fun x => f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      (volume : Measure EuclN) := by
    have h := (hf₂_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)))
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  have hint_g1_φ : Integrable
      (fun x => g₁ x * φ x) (volume : Measure EuclN) := by
    have h := hg₁_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_supp)
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  have hint_g2_φ : Integrable
      (fun x => g₂ x * φ x) (volume : Measure EuclN) := by
    have h := hg₂_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_supp)
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  have h_lhs_split :
      ∫ x, (f₁ + f₂) x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        (∫ x, f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) +
          ∫ x, f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    have h_eq : (fun x => (f₁ + f₂) x *
        (fderiv ℝ φ x) (EuclideanSpace.single j 1)) =
      fun x => f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
        f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
      ext x
      change (f₁ x + f₂ x) *
          (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        f₁ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) +
          f₂ x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)
      ring
    rw [h_eq, integral_add hint_f1_partial hint_f2_partial]
  rw [h_lhs_split]
  have h_rhs_split :
      ∫ x, (g₁ + g₂) x * φ x =
        (∫ x, g₁ x * φ x) + ∫ x, g₂ x * φ x := by
    have h_eq : (fun x => (g₁ + g₂) x * φ x) =
      fun x => g₁ x * φ x + g₂ x * φ x := by
      ext x
      change (g₁ x + g₂ x) * φ x = g₁ x * φ x + g₂ x * φ x
      ring
    rw [h_eq, integral_add hint_g1_φ hint_g2_φ]
  rw [h_rhs_split, neg_add]
  linarith

omit [NeZero d] in
theorem hasWeakPartialDeriv_const_smul_univ
    (j : Fin d) (c : ℝ) {f g : EuclN → ℝ}
    (hf_locInt :
      LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ))
    (hg_locInt :
      LocallyIntegrable g ((volume : Measure EuclN).restrict Set.univ))
    (h1 : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g f Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (fun x => c * g x) (fun x => c * f x) Set.univ := by
  intro φ hφ_smooth hφ_supp _hφ_sub
  have heq := h1 φ hφ_smooth hφ_supp (tsupport_subset_univ φ)
  rw [setIntegral_univ, setIntegral_univ] at heq
  rw [setIntegral_univ, setIntegral_univ]
  have hint_f_partial : Integrable
      (fun x => f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1))
      (volume : Measure EuclN) := by
    have h := (hf_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := (hφ_smooth.continuous_fderiv (by simp)).clm_apply
        continuous_const)
      (h'g := hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single j 1)))
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  have hint_g_φ : Integrable
      (fun x => g x * φ x) (volume : Measure EuclN) := by
    have h := hg_locInt.integrable_smul_right_of_hasCompactSupport
      (hg := hφ_smooth.continuous) (h'g := hφ_supp)
    simpa [Measure.restrict_univ, smul_eq_mul] using h
  let _ := hint_f_partial
  let _ := hint_g_φ
  have h_lhs_pull :
      ∫ x, (c * f x) * (fderiv ℝ φ x) (EuclideanSpace.single j 1) =
        c * ∫ x, f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1) := by
    have h_eq : (fun x => (c * f x) *
        (fderiv ℝ φ x) (EuclideanSpace.single j 1)) =
      fun x => c * (f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) := by
      ext x; ring
    rw [h_eq, integral_const_mul]
  rw [h_lhs_pull]
  have h_rhs_pull :
      ∫ x, (c * g x) * φ x = c * ∫ x, g x * φ x := by
    have h_eq : (fun x => (c * g x) * φ x) =
      fun x => c * (g x * φ x) := by ext x; ring
    rw [h_eq, integral_const_mul]
  rw [h_rhs_pull]
  have : c * (∫ x, f x * (fderiv ℝ φ x) (EuclideanSpace.single j 1)) =
      c * (-(∫ x, g x * φ x)) := by rw [heq]
  rw [this, mul_neg]

omit [NeZero d] in
private lemma locallyIntegrable_univ_of_memLp
    {f : EuclN → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hf : MemLp f p (volume : Measure EuclN)) :
    LocallyIntegrable f ((volume : Measure EuclN).restrict Set.univ) := by
  rw [Measure.restrict_univ]
  exact hf.locallyIntegrable hp

omit [NeZero d] in
private lemma locallyIntegrable_translate_aux
    (k : Fin d) (h : ℝ) {u : EuclN → ℝ}
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ)) :
    LocallyIntegrable (translate k h u)
      ((volume : Measure EuclN).restrict Set.univ) := by
  rw [Measure.restrict_univ] at hu_locInt ⊢
  have hMP : MeasurePreserving
      (fun x : EuclN => x + h • EuclideanSpace.single k 1) volume volume :=
    measurePreserving_add_right volume _
  let τ : EuclN ≃ₜ EuclN :=
    Homeomorph.addRight (h • EuclideanSpace.single k 1)
  have hτ_eq : ⇑τ = fun x : EuclN => x + h • EuclideanSpace.single k 1 := rfl
  have hτ_emb : MeasurableEmbedding τ := τ.measurableEmbedding
  have hMP_τ : MeasurePreserving τ volume volume := by
    rw [show (τ : EuclN → EuclN) = fun x => x + h • EuclideanSpace.single k 1
      from rfl]
    exact hMP
  intro x
  obtain ⟨V, hV_mem, hf_int⟩ := hu_locInt (τ x)
  refine ⟨τ ⁻¹' V, ?_, ?_⟩
  · exact τ.continuous.continuousAt.preimage_mem_nhds hV_mem
  · have h_eq : translate k h u = u ∘ (τ : EuclN → EuclN) := rfl
    rw [h_eq]
    exact (hMP_τ.integrableOn_comp_preimage hτ_emb (f := u) (s := V)).mpr hf_int

omit [NeZero d] in
theorem hasWeakPartialDeriv_diffQuot
    (k j : Fin d) (h : ℝ) {u g_j : EuclN → ℝ}
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (diffQuot k h g_j) (diffQuot k h u) Set.univ := by
  by_cases hh : h = 0
  · subst hh
    simp only [diffQuot_zero_h]
    intro φ _ _ _
    rw [setIntegral_univ, setIntegral_univ]
    simp
  · have h_diffQuot_u_eq : diffQuot k h u =
        fun x => h⁻¹ * (translate k h u x) + (-h⁻¹) * u x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh u x]
      have htrans_x : translate k h u x =
          u (x + h • EuclideanSpace.single k 1) := rfl
      rw [htrans_x]
      field_simp
      ring
    have h_diffQuot_g_eq : diffQuot k h g_j =
        fun x => h⁻¹ * (translate k h g_j x) + (-h⁻¹) * g_j x := by
      funext x
      rw [diffQuot_apply_of_ne (d := d) k hh g_j x]
      have htrans_x : translate k h g_j x =
          g_j (x + h • EuclideanSpace.single k 1) := rfl
      rw [htrans_x]
      field_simp
      ring
    rw [h_diffQuot_u_eq, h_diffQuot_g_eq]
    have h_translate :
        Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
          (translate k h g_j) (translate k h u) Set.univ := by
      have h_neg_neg : -(-h) = h := neg_neg h
      have h_eq_u : translate k h u = translate k (-(-h)) u := by rw [h_neg_neg]
      have h_eq_g : translate k h g_j = translate k (-(-h)) g_j := by rw [h_neg_neg]
      rw [h_eq_u, h_eq_g]
      exact hasWeakPartialDeriv_translate (d := d) k j (-h) hwp
    have h_translate_u_locInt :
        LocallyIntegrable (translate k h u)
          ((volume : Measure EuclN).restrict Set.univ) :=
      locallyIntegrable_translate_aux (d := d) k h hu_locInt
    have h_translate_g_locInt :
        LocallyIntegrable (translate k h g_j)
          ((volume : Measure EuclN).restrict Set.univ) :=
      locallyIntegrable_translate_aux (d := d) k h hg_j_locInt
    have h_smul_translate :
        Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
          (fun x => h⁻¹ * translate k h g_j x)
          (fun x => h⁻¹ * translate k h u x) Set.univ :=
      hasWeakPartialDeriv_const_smul_univ (d := d) j h⁻¹
        h_translate_u_locInt h_translate_g_locInt h_translate
    have h_smul_orig :
        Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
          (fun x => (-h⁻¹) * g_j x)
          (fun x => (-h⁻¹) * u x) Set.univ :=
      hasWeakPartialDeriv_const_smul_univ (d := d) j (-h⁻¹)
        hu_locInt hg_j_locInt hwp
    have h_smul_translate_u_locInt :
        LocallyIntegrable (fun x : EuclN => h⁻¹ * translate k h u x)
          ((volume : Measure EuclN).restrict Set.univ) := by
      have h_eq : (fun x : EuclN => h⁻¹ * translate k h u x) =
          h⁻¹ • translate k h u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact h_translate_u_locInt.smul h⁻¹
    have h_smul_translate_g_locInt :
        LocallyIntegrable (fun x : EuclN => h⁻¹ * translate k h g_j x)
          ((volume : Measure EuclN).restrict Set.univ) := by
      have h_eq : (fun x : EuclN => h⁻¹ * translate k h g_j x) =
          h⁻¹ • translate k h g_j := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact h_translate_g_locInt.smul h⁻¹
    have h_smul_orig_u_locInt :
        LocallyIntegrable (fun x : EuclN => (-h⁻¹) * u x)
          ((volume : Measure EuclN).restrict Set.univ) := by
      have h_eq : (fun x : EuclN => (-h⁻¹) * u x) =
          (-h⁻¹) • u := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact hu_locInt.smul (-h⁻¹)
    have h_smul_orig_g_locInt :
        LocallyIntegrable (fun x : EuclN => (-h⁻¹) * g_j x)
          ((volume : Measure EuclN).restrict Set.univ) := by
      have h_eq : (fun x : EuclN => (-h⁻¹) * g_j x) =
          (-h⁻¹) • g_j := by
        funext x; rw [Pi.smul_apply, smul_eq_mul]
      rw [h_eq]
      exact hg_j_locInt.smul (-h⁻¹)
    have h_add :=
      hasWeakPartialDeriv_add_univ (d := d) j
        h_smul_translate_u_locInt h_smul_orig_u_locInt
        h_smul_translate_g_locInt h_smul_orig_g_locInt
        h_smul_translate h_smul_orig
    exact h_add

omit [NeZero d] in
private lemma contDiff_eta_sq {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (η y)^2) := hη.pow 2

omit [NeZero d] in
private lemma fderiv_eta_sq_apply {η : EuclN → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (j : Fin d) (x : EuclN) :
    (fderiv ℝ (fun y : EuclN => (η y)^2) x) (EuclideanSpace.single j 1) =
      2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) := by
  have hη_diff : Differentiable ℝ η := hη.differentiable (by simp)
  rw [fderiv_fun_pow 2 (hη_diff x)]
  rw [smul_apply]
  have h1 : (η x) ^ ((2 : ℕ) - 1) = η x := by norm_num
  rw [h1]
  have h_two : ((2 : ℕ) • η x) = 2 * η x := by
    rw [two_smul]; ring
  rw [h_two, smul_eq_mul]

omit [NeZero d] in
theorem hasWeakPartialDeriv_eta_sq_diffQuot
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (fun y => (η y)^2 * diffQuot k h g_j y +
        ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
          diffQuot k h u y)
      (fun y => (η y)^2 * diffQuot k h u y) Set.univ := by
  have h_wp_dq :
      Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
        (diffQuot k h g_j) (diffQuot k h u) Set.univ :=
    hasWeakPartialDeriv_diffQuot (d := d) k j h hu_locInt hg_j_locInt hwp
  have h_dq_u_locInt :
      LocallyIntegrable (diffQuot k h u)
        ((volume : Measure EuclN).restrict Set.univ) := by
    by_cases hh : h = 0
    · subst hh; rw [diffQuot_zero_h]
      rw [Measure.restrict_univ]
      exact locallyIntegrable_const _
    · have h_eq : diffQuot k h u =
          fun x => h⁻¹ * (translate k h u x) + (-h⁻¹) * u x := by
        funext x
        rw [diffQuot_apply_of_ne (d := d) k hh u x]
        change (u (x + h • EuclideanSpace.single k 1) - u x) / h =
          h⁻¹ * u (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * u x
        field_simp; ring
      rw [h_eq]
      have h_translate_locInt :
          LocallyIntegrable (translate k h u)
            ((volume : Measure EuclN).restrict Set.univ) :=
        locallyIntegrable_translate_aux (d := d) k h hu_locInt
      have hmul1 :
          LocallyIntegrable (fun x : EuclN => h⁻¹ * translate k h u x)
            ((volume : Measure EuclN).restrict Set.univ) := by
        have h_eq_smul : (fun x : EuclN => h⁻¹ * translate k h u x) =
            h⁻¹ • translate k h u := by
          funext x; rw [Pi.smul_apply, smul_eq_mul]
        rw [h_eq_smul]
        exact h_translate_locInt.smul h⁻¹
      have hmul2 :
          LocallyIntegrable (fun x : EuclN => (-h⁻¹) * u x)
            ((volume : Measure EuclN).restrict Set.univ) := by
        have h_eq_smul : (fun x : EuclN => (-h⁻¹) * u x) = (-h⁻¹) • u := by
          funext x; rw [Pi.smul_apply, smul_eq_mul]
        rw [h_eq_smul]
        exact hu_locInt.smul (-h⁻¹)
      exact hmul1.add hmul2
  have h_dq_g_locInt :
      LocallyIntegrable (diffQuot k h g_j)
        ((volume : Measure EuclN).restrict Set.univ) := by
    by_cases hh : h = 0
    · subst hh; rw [diffQuot_zero_h]
      rw [Measure.restrict_univ]
      exact locallyIntegrable_const _
    · have h_eq : diffQuot k h g_j =
          fun x => h⁻¹ * (translate k h g_j x) + (-h⁻¹) * g_j x := by
        funext x
        rw [diffQuot_apply_of_ne (d := d) k hh g_j x]
        change (g_j (x + h • EuclideanSpace.single k 1) - g_j x) / h =
          h⁻¹ * g_j (x + h • EuclideanSpace.single k 1) + (-h⁻¹) * g_j x
        field_simp; ring
      rw [h_eq]
      have h_translate_locInt :
          LocallyIntegrable (translate k h g_j)
            ((volume : Measure EuclN).restrict Set.univ) :=
        locallyIntegrable_translate_aux (d := d) k h hg_j_locInt
      have hmul1 :
          LocallyIntegrable (fun x : EuclN => h⁻¹ * translate k h g_j x)
            ((volume : Measure EuclN).restrict Set.univ) := by
        have h_eq_smul : (fun x : EuclN => h⁻¹ * translate k h g_j x) =
            h⁻¹ • translate k h g_j := by
          funext x; rw [Pi.smul_apply, smul_eq_mul]
        rw [h_eq_smul]
        exact h_translate_locInt.smul h⁻¹
      have hmul2 :
          LocallyIntegrable (fun x : EuclN => (-h⁻¹) * g_j x)
            ((volume : Measure EuclN).restrict Set.univ) := by
        have h_eq_smul : (fun x : EuclN => (-h⁻¹) * g_j x) = (-h⁻¹) • g_j := by
          funext x; rw [Pi.smul_apply, smul_eq_mul]
        rw [h_eq_smul]
        exact hg_j_locInt.smul (-h⁻¹)
      exact hmul1.add hmul2
  have h_eta_sq_smooth : ContDiff ℝ (⊤ : ℕ∞) (fun y : EuclN => (η y)^2) :=
    hη.pow 2
  exact Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv.mul_smooth (Ω := Set.univ) isOpen_univ
    h_wp_dq h_eta_sq_smooth h_dq_u_locInt h_dq_g_locInt

omit [NeZero d] in
theorem hasWeakPartialDeriv_nirenbergTestFunction
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (translate k (-h)
        (fun y => (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y))
      (nirenbergTestFunction k h η u) Set.univ := by
  have h_inner_wp :=
    hasWeakPartialDeriv_eta_sq_diffQuot (d := d) k j h hη
      hu_locInt hg_j_locInt hwp
  unfold nirenbergTestFunction
  exact hasWeakPartialDeriv_translate (d := d) k j h h_inner_wp

omit [NeZero d] in
theorem hasWeakPartialDeriv_nirenbergTestFunction_expanded
    (k j : Fin d) (h : ℝ) {η u g_j : EuclN → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hu_locInt :
      LocallyIntegrable u ((volume : Measure EuclN).restrict Set.univ))
    (hg_j_locInt :
      LocallyIntegrable g_j ((volume : Measure EuclN).restrict Set.univ))
    (hwp : Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j g_j u Set.univ) :
    Poincare.Analysis.Sobolev.Weak.HasWeakPartialDeriv (d := d) j
      (translate k (-h)
        (fun y =>
          (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y))
      (nirenbergTestFunction k h η u) Set.univ := by
  have h_general :=
    hasWeakPartialDeriv_nirenbergTestFunction (d := d) k j h hη
      hu_locInt hg_j_locInt hwp
  have h_eq :
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          ((fderiv ℝ (fun z => (η z)^2) y) (EuclideanSpace.single j 1)) *
            diffQuot k h u y) =
      (fun y : EuclN =>
        (η y)^2 * diffQuot k h g_j y +
          2 * η y * (fderiv ℝ η y) (EuclideanSpace.single j 1) *
            diffQuot k h u y) := by
    funext y
    rw [fderiv_eta_sq_apply (d := d) hη j y]
  rw [h_eq] at h_general
  exact h_general

omit [NeZero d] in
example (k : Fin d) (η u : EuclN → ℝ) :
    nirenbergTestFunction k 0 η u = 0 := by
  funext x
  simp [nirenbergTestFunction, translate, diffQuot]

end Poincare.Analysis.Sobolev.NirenbergDiffQuotTestFunction
