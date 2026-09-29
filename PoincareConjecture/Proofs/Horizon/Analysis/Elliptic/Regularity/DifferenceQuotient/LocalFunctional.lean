/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Tools/DifferenceQuotientWeakLimitLoc.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development. The local file extracts a subset of the upstream development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.TestSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Poincare.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
lemma integrable_w_partial_phi_loc
    {Ω : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (k : Fin d) :
    Integrable (fun x => w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))
      ((volume : Measure E).restrict Ω) := by
  have h_partial_cont : Continuous
      (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    (hφ_smooth.continuous_fderiv (by simp : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0)).clm_apply
      continuous_const
  have h_partial_supp :
      HasCompactSupport (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) :=
    hφ_supp.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single k 1)
  have h_partial_memLp :
      MemLp (fun x : E => (fderiv ℝ φ x) (EuclideanSpace.single k 1)) 2
        ((volume : Measure E).restrict Ω) :=
    (h_partial_cont.memLp_of_hasCompactSupport h_partial_supp).restrict _
  exact MemLp.integrable_mul hw_l2 h_partial_memLp

def smoothTestFunctionalLoc
    {Ω Ω'' : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    smoothCSSupportedInSubmodule (d := d) Ω'' →ₗ[ℝ] ℝ where
  toFun φ :=
    -∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
      ∂(volume : Measure E)
  map_add' φ ψ := by
    change
      -∫ x in Ω, w x *
        (fderiv ℝ ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
          (EuclideanSpace.single k 1) ∂(volume : Measure E) =
      (-∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E)) +
      (-∫ x in Ω, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have hψ_diff : Differentiable ℝ ψ.1 := ψ.2.1.differentiable (by simp)
    have h_fderiv_sum : ∀ x : E,
        (fderiv ℝ ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1) =
          (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      have hcoe : ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1 : E → ℝ) =
          φ.1 + ψ.1 := rfl
      rw [hcoe]
      rw [show (φ.1 + ψ.1 : E → ℝ) = fun y => φ.1 y + ψ.1 y from rfl]
      rw [fderiv_fun_add (hφ_diff.differentiableAt) (hψ_diff.differentiableAt)]
      simp
    have hint_sum : ∀ x : E,
        w x * (fderiv ℝ ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) =
          w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
            w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1) := by
      intro x; rw [h_fderiv_sum x]; ring
    have hφ_int := integrable_w_partial_phi_loc (d := d) hw_l2 φ.2.1 φ.2.2.1 k
    have hψ_int := integrable_w_partial_phi_loc (d := d) hw_l2 ψ.2.1 ψ.2.2.1 k
    have h_int_eq :
        ∫ x in Ω, w x *
            (fderiv ℝ ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) ∂(volume : Measure E) =
          (∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E)) +
            ∫ x in Ω, w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((φ + ψ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1)) =
        (fun x =>
            w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) +
              w x * (fderiv ℝ ψ.1 x) (EuclideanSpace.single k 1)) from by
          ext x; exact hint_sum x]
      exact integral_add hφ_int hψ_int
    rw [h_int_eq]; ring
  map_smul' c φ := by
    change
      -∫ x in Ω, w x *
        (fderiv ℝ ((c • φ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
          (EuclideanSpace.single k 1) ∂(volume : Measure E) =
      c • (-∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E))
    have hφ_diff : Differentiable ℝ φ.1 := φ.2.1.differentiable (by simp)
    have h_fderiv_smul : ∀ x : E,
        (fderiv ℝ ((c • φ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1) =
          c * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1) := by
      intro x
      have hcoe : ((c • φ : smoothCSSupportedInSubmodule (d := d) Ω'').1
          : E → ℝ) = c • φ.1 := rfl
      rw [hcoe]
      have heq2 : (c • φ.1 : E → ℝ) = fun y => c * φ.1 y := by ext y; rfl
      rw [heq2]
      rw [fderiv_const_mul (hφ_diff.differentiableAt) c]
      simp
    have hint_smul : ∀ x : E,
        w x * (fderiv ℝ ((c • φ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) =
          c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)) := by
      intro x; rw [h_fderiv_smul x]; ring
    have h_int_eq :
        ∫ x in Ω, w x * (fderiv ℝ ((c • φ : smoothCSSupportedInSubmodule
            (d := d) Ω'').1) x)
              (EuclideanSpace.single k 1) ∂(volume : Measure E) =
          c * ∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      rw [show (fun x => w x *
          (fderiv ℝ ((c • φ : smoothCSSupportedInSubmodule (d := d) Ω'').1) x)
            (EuclideanSpace.single k 1)) =
        (fun x => c * (w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)))
          from by ext x; exact hint_smul x]
      exact integral_const_mul _ _
    rw [h_int_eq]
    rw [smul_eq_mul]; ring

omit [NeZero d] in
@[simp] lemma smoothTestFunctional_loc_apply
    {Ω Ω'' : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) (φ : smoothCSSupportedInSubmodule (d := d) Ω'') :
    smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ =
      -∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E) := rfl

omit [NeZero d] in
lemma diffQuot_eq_zero_of_notMem_cthickening_loc
    {φ : E → ℝ} (_hφ_supp : HasCompactSupport φ)
    (k : Fin d) {h₀ : ℝ} (_hh₀ : 0 ≤ h₀) {h : ℝ} (hh_bd : |h| ≤ h₀) :
    ∀ x : E, x ∉ Metric.cthickening h₀ (tsupport φ) →
      diffQuot k h φ x = 0 := by
  intro x hx
  have hxnot : x ∉ tsupport φ := fun h => hx (Metric.self_subset_cthickening _ h)
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hxnot
  have hxhe : x + h • EuclideanSpace.single k 1 ∉ tsupport φ := by
    intro hin
    apply hx
    have hnorm :
        dist x (x + h • EuclideanSpace.single k 1) = |h| := by
      rw [dist_eq_norm]
      have heq : x - (x + h • EuclideanSpace.single k 1) =
          -(h • EuclideanSpace.single k 1) := by abel
      rw [heq, norm_neg, norm_smul]
      rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
      rw [Real.norm_eq_abs, mul_one]
    have h_dist_le : dist x (x + h • EuclideanSpace.single k 1) ≤ h₀ := by
      rw [hnorm]; exact hh_bd
    exact Metric.mem_cthickening_of_dist_le x
      (x + h • EuclideanSpace.single k 1) h₀ (tsupport φ) hin h_dist_le
  have hφxhe : φ (x + h • EuclideanSpace.single k 1) = 0 :=
    image_eq_zero_of_notMem_tsupport hxhe
  by_cases hh : h = 0
  · rw [hh]; simp [diffQuot]
  · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
    rw [hφx, hφxhe]
    simp

omit [NeZero d] in
lemma tendsto_integral_w_diffQuot_phi_loc
    {Ω : Set E} {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    {φ : E → ℝ} (hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hφ_supp : HasCompactSupport φ) (k : Fin d)
    {hₙ : ℕ → ℝ} (hₙ_ne : ∀ n, hₙ n ≠ 0)
    (hₙ_tendsto : Tendsto hₙ atTop (𝓝 0)) :
    Tendsto (fun n =>
        ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ x ∂(volume : Measure E))
      atTop
      (𝓝 (∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) := by
  have hφ_C1 : ContDiff ℝ 1 φ := hφ_smooth.of_le (by norm_cast)
  have h_lip : ∃ L : ℝ, 0 ≤ L ∧ ∀ h : ℝ, ∀ x : E, |diffQuot k h φ x| ≤ L := by
    obtain ⟨L, hL_nn, hLip⟩ :=
      lipschitz_of_contDiff_compactSupport (d := d) hφ_C1 hφ_supp
    refine ⟨L, hL_nn, fun h x => ?_⟩
    by_cases hh : h = 0
    · rw [hh, diffQuot_zero_h]; simpa using hL_nn
    · rw [diffQuot_apply_of_ne (d := d) k hh φ x]
      have hLip_apply :
          ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ ≤
            L * ‖x + h • EuclideanSpace.single k 1 - x‖ := hLip _ _
      have hsimp : x + h • EuclideanSpace.single k 1 - x =
          h • EuclideanSpace.single k 1 := by
        rw [add_sub_cancel_left]
      rw [hsimp] at hLip_apply
      have hsing_norm :
          ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 := by simp
      have hnorm_smul :
          ‖h • EuclideanSpace.single k (1 : ℝ)‖ = |h| := by
        rw [norm_smul, hsing_norm, mul_one, Real.norm_eq_abs]
      rw [hnorm_smul] at hLip_apply
      rw [abs_div]
      have habs_h : 0 < |h| := abs_pos.mpr hh
      rw [div_le_iff₀ habs_h]
      have h_lhs_norm :
          |φ (x + h • EuclideanSpace.single k 1) - φ x| =
            ‖φ (x + h • EuclideanSpace.single k 1) - φ x‖ :=
        (Real.norm_eq_abs _).symm
      rw [h_lhs_norm]
      exact hLip_apply
  obtain ⟨L, _hL_nn, hLip⟩ := h_lip
  set h₀ : ℝ := 1 with h₀_def
  have hh₀_nn : (0 : ℝ) ≤ h₀ := by simp [h₀_def]
  have hN : ∀ᶠ n in atTop, |hₙ n| ≤ h₀ := by
    have hAbs : Tendsto (fun n => |hₙ n|) atTop (𝓝 0) := by
      have := hₙ_tendsto.abs; simpa using this
    have h_ev :
        ∀ᶠ n in atTop, dist (|hₙ n|) 0 < 1 :=
      hAbs.eventually (Metric.ball_mem_nhds 0 (by norm_num))
    filter_upwards [h_ev] with n hn
    have h_dist : dist (|hₙ n|) 0 = |hₙ n| := by
      rw [Real.dist_eq, sub_zero, abs_abs]
    rw [h_dist] at hn
    exact hn.le
  set K_thick : Set E := Metric.cthickening h₀ (tsupport φ) with hKt_def
  have hK_compact : IsCompact (tsupport φ) := hφ_supp
  have hK_thick_compact : IsCompact K_thick := hK_compact.cthickening
  have hK_thick_meas : MeasurableSet K_thick :=
    hK_thick_compact.measurableSet
  set bound : E → ℝ := fun x => K_thick.indicator (fun y => L * |w y|) x
  have hw_meas : AEStronglyMeasurable w ((volume : Measure E).restrict Ω) :=
    hw_l2.aestronglyMeasurable
  have h_indicator_memLp_2 :
      MemLp (fun x : E => K_thick.indicator (fun _ => (1 : ℝ)) x) 2
        ((volume : Measure E).restrict Ω) := by
    have h_finite : ((volume : Measure E).restrict Ω) K_thick ≠ ∞ := by
      have h₁ : ((volume : Measure E).restrict Ω) K_thick ≤
          (volume : Measure E) K_thick := Measure.restrict_le_self _
      exact ne_top_of_le_ne_top hK_thick_compact.measure_lt_top.ne h₁
    refine memLp_indicator_const _ hK_thick_meas (1 : ℝ) (Or.inr h_finite)
  have h_abs_eq_norm : (fun x => |w x|) = fun x => ‖w x‖ := by
    funext x; rw [Real.norm_eq_abs]
  have h_abs_w_memLp : MemLp (fun x => |w x|) 2
      ((volume : Measure E).restrict Ω) := by
    rw [h_abs_eq_norm]
    exact hw_l2.norm
  have h_Labsw_memLp :
      MemLp (fun x => L * |w x|) 2 ((volume : Measure E).restrict Ω) :=
    h_abs_w_memLp.const_mul L
  have h_bound_eq :
      bound = (fun x => (L * |w x|) *
        K_thick.indicator (fun _ => (1 : ℝ)) x) := by
    funext x
    simp only [bound]
    by_cases hx : x ∈ K_thick
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
  have h_bound_int : Integrable bound ((volume : Measure E).restrict Ω) := by
    rw [h_bound_eq]
    exact MemLp.integrable_mul h_Labsw_memLp h_indicator_memLp_2
  have h_pointwise_bound :
      ∀ᶠ n in atTop, ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        ‖w x * diffQuot k (-(hₙ n)) φ x‖ ≤ bound x := by
    filter_upwards [hN] with n hn
    refine Filter.Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ K_thick
    · simp only [bound, Set.indicator_of_mem hx]
      rw [Real.norm_eq_abs, abs_mul]
      have hL_dq : |diffQuot k (-(hₙ n)) φ x| ≤ L := hLip _ x
      have h_abs_w_nn : 0 ≤ |w x| := abs_nonneg _
      have h_LL : |w x| * |diffQuot k (-(hₙ n)) φ x| ≤ |w x| * L :=
        mul_le_mul_of_nonneg_left hL_dq h_abs_w_nn
      linarith
    · have h_neg_h_bd : |-(hₙ n)| ≤ h₀ := by rw [abs_neg]; exact hn
      have hdq_zero : diffQuot k (-(hₙ n)) φ x = 0 :=
        diffQuot_eq_zero_of_notMem_cthickening_loc (d := d) hφ_supp k hh₀_nn
          h_neg_h_bd x hx
      rw [hdq_zero, mul_zero, norm_zero]
      simp [bound, Set.indicator_of_notMem hx]
  have h_pointwise_conv :
      ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        Tendsto (fun n => w x * diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 (w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1))) := by
    refine Filter.Eventually.of_forall fun x => ?_
    have h_minus_tendsto : Tendsto (fun n => -(hₙ n)) atTop (𝓝 0) := by
      have := hₙ_tendsto.neg; simpa using this
    have h_minus_ne : ∀ n, -(hₙ n) ≠ 0 := fun n hn =>
      hₙ_ne n (neg_eq_zero.mp hn)
    have h_dq_nhdsWithin :
        Tendsto (fun h : ℝ => diffQuot k h φ x) (𝓝[≠] 0)
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      tendsto_diffQuot_of_contDiff (d := d) hφ_C1 k x
    have h_tendsto_within :
        Tendsto (fun n => -(hₙ n)) atTop (𝓝[≠] 0) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨h_minus_tendsto, ?_⟩
      exact Filter.Eventually.of_forall fun n => h_minus_ne n
    have h_dq_tendsto :
        Tendsto (fun n => diffQuot k (-(hₙ n)) φ x) atTop
          (𝓝 ((fderiv ℝ φ x) (EuclideanSpace.single k 1))) :=
      h_dq_nhdsWithin.comp h_tendsto_within
    exact h_dq_tendsto.const_mul (w x)
  have h_aesm_seq : ∀ n, AEStronglyMeasurable
      (fun x => w x * diffQuot k (-(hₙ n)) φ x)
      ((volume : Measure E).restrict Ω) := by
    intro n
    have hdq_global : AEStronglyMeasurable (diffQuot k (-(hₙ n)) φ)
        (volume : Measure E) :=
      aestronglyMeasurable_diffQuot (d := d) k _
        hφ_smooth.continuous.aestronglyMeasurable
    have hdq_meas : AEStronglyMeasurable (diffQuot k (-(hₙ n)) φ)
        ((volume : Measure E).restrict Ω) := hdq_global.restrict
    exact hw_meas.mul hdq_meas
  exact tendsto_integral_filter_of_dominated_convergence
    bound (Filter.Eventually.of_forall h_aesm_seq)
    h_pointwise_bound h_bound_int h_pointwise_conv

omit [NeZero d] in
lemma abs_integral_mul_le_eLpNorm_two_loc
    {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ eLpNorm f 2 μ * eLpNorm g 2 μ := by
  have h_abs_le_lintegral :
      ENNReal.ofReal |∫ x, f x * g x ∂μ| ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := by
    rw [← Real.norm_eq_abs]
    have hint : ‖∫ x, f x * g x ∂μ‖ₑ ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ :=
      enorm_integral_le_lintegral_enorm _
    have hofreal : ENNReal.ofReal ‖∫ x, f x * g x ∂μ‖ = ‖∫ x, f x * g x ∂μ‖ₑ :=
      ofReal_norm _
    rw [hofreal]; exact hint
  have h_lintegral_eq :
      ∫⁻ x, ‖f x * g x‖ₑ ∂μ = eLpNorm (fun x => g x * f x) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm]
    refine lintegral_congr (fun x => ?_)
    simp [enorm_mul, mul_comm]
  have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := by
    constructor
    rw [show (1 : ℝ≥0∞)⁻¹ = 1 from inv_one]
    rw [ENNReal.inv_two_add_inv_two]
  have h_smul_bound :
      eLpNorm (fun x => g x * f x) 1 μ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := by
    have h_mul_eq :
        (fun x => g x * f x) = (g : E → ℝ) • (f : E → ℝ) := by
      funext x; simp [smul_eq_mul]
    rw [h_mul_eq]
    have : ENNReal.HolderTriple (2 : ℝ≥0∞) (2 : ℝ≥0∞) 1 := inferInstance
    exact eLpNorm_smul_le_mul_eLpNorm hf.aestronglyMeasurable hg.aestronglyMeasurable
  calc
    ENNReal.ofReal |∫ x, f x * g x ∂μ|
        ≤ ∫⁻ x, ‖f x * g x‖ₑ ∂μ := h_abs_le_lintegral
    _ = eLpNorm (fun x => g x * f x) 1 μ := h_lintegral_eq
    _ ≤ eLpNorm g 2 μ * eLpNorm f 2 μ := h_smul_bound
    _ = eLpNorm f 2 μ * eLpNorm g 2 μ := mul_comm _ _

omit [NeZero d] in
lemma abs_integral_mul_le_norm_lp_mul_norm_lp_loc
    {μ : Measure E} {f g : E → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    |∫ x, f x * g x ∂μ| ≤
      (eLpNorm f 2 μ).toReal * (eLpNorm g 2 μ).toReal := by
  have h_ennreal := abs_integral_mul_le_eLpNorm_two_loc (μ := μ) hf hg
  have h_finite_f : eLpNorm f 2 μ ≠ ∞ := hf.eLpNorm_lt_top.ne
  have h_finite_g : eLpNorm g 2 μ ≠ ∞ := hg.eLpNorm_lt_top.ne
  have h_finite : eLpNorm f 2 μ * eLpNorm g 2 μ ≠ ∞ :=
    ENNReal.mul_ne_top h_finite_f h_finite_g
  have h_toReal := ENNReal.toReal_mono h_finite h_ennreal
  have hnn : 0 ≤ |∫ x, f x * g x ∂μ| := abs_nonneg _
  rw [ENNReal.toReal_ofReal hnn] at h_toReal
  rw [ENNReal.toReal_mul] at h_toReal
  exact h_toReal

omit [NeZero d] in
lemma abs_smoothTestFunctional_loc_le
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCSSupportedInSubmodule (d := d) Ω'') :
    |smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ| ≤
      M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
  let _ := hΩ_open
  let _ := hΩ''_open
  let _ := hΩ''_compact_closure
  rw [smoothTestFunctional_loc_apply]
  rw [abs_neg]
  set hₙ : ℕ → ℝ := fun n => h₀ / (n + 1)
  have hₙ_pos : ∀ n, 0 < hₙ n := fun n => by
    apply div_pos hh₀
    have : (0 : ℝ) < n + 1 := by exact_mod_cast Nat.zero_lt_succ n
    exact this
  have hₙ_ne : ∀ n, hₙ n ≠ 0 := fun n => (hₙ_pos n).ne'
  have hₙ_bd : ∀ n, |hₙ n| ≤ h₀ := fun n => by
    rw [abs_of_pos (hₙ_pos n)]
    have h1 : (1 : ℝ) ≤ n + 1 := by
      have h0 : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le (n := n)
      linarith
    rw [div_le_iff₀ (by exact_mod_cast Nat.zero_lt_succ n : (0 : ℝ) < n + 1)]
    have : h₀ ≤ h₀ * (n + 1) := by nlinarith [hh₀.le]
    linarith
  have hₙ_pos_abs : ∀ n, 0 < |hₙ n| := fun n => by
    rw [abs_of_pos (hₙ_pos n)]; exact hₙ_pos n
  have hₙ_tendsto : Tendsto hₙ atTop (𝓝 0) := by
    have hh0 : Tendsto (fun n : ℕ => (1 : ℝ) / (↑n + 1)) atTop (𝓝 (0 : ℝ)) := by
      have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
      exact this
    have h_eq : ∀ n, hₙ n = h₀ * (1 / ((n : ℝ) + 1)) := fun n => by
      simp only [hₙ]; ring
    rw [show hₙ = fun n : ℕ => h₀ * (1 / ((↑n : ℝ) + 1)) from funext h_eq]
    have hmul := hh0.const_mul h₀
    simpa using hmul
  have hφ_memLp : MemLp φ.1 2 ((volume : Measure E).restrict Ω'') :=
    memLp_two_restrict_of_smoothCS (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1
  have hφ_memLp_global : MemLp φ.1 2 (volume : Measure E) :=
    φ.2.1.continuous.memLp_of_hasCompactSupport φ.2.2.1
  have h_conv : Tendsto (fun n =>
      ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)) atTop
      (𝓝 (∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
        ∂(volume : Measure E))) :=
    tendsto_integral_w_diffQuot_phi_loc (d := d) hw_l2 φ.2.1 φ.2.2.1 k hₙ_ne hₙ_tendsto
  have h_dq_l2_bound : ∀ n,
      eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M := fun n =>
    h_bdd (hₙ n) (hₙ_pos_abs n) (hₙ_bd n)
  set w_ext : E → ℝ := fun x => Ω.indicator w x with hw_ext_def
  have hw_ext_eq_w_on_Ω : ∀ x ∈ Ω, w_ext x = w x := by
    intro x hx
    simp only [w_ext, Set.indicator_of_mem hx]
  have hw_ext_zero_off_Ω : ∀ x ∉ Ω, w_ext x = 0 := by
    intro x hx
    simp only [w_ext, Set.indicator_of_notMem hx]
  have hw_ext_memLp : MemLp w_ext 2 (volume : Measure E) := by
    have h_aesm : AEStronglyMeasurable w_ext (volume : Measure E) := by
      have h_w_aesm : AEStronglyMeasurable w ((volume : Measure E).restrict Ω) :=
        hw_l2.aestronglyMeasurable
      exact (aestronglyMeasurable_indicator_iff hΩ_open.measurableSet).mpr h_w_aesm
    refine ⟨h_aesm, ?_⟩
    have h_eLpNorm_eq :
        eLpNorm w_ext 2 (volume : Measure E) =
          eLpNorm w 2 ((volume : Measure E).restrict Ω) := by
      rw [show w_ext = fun x => Ω.indicator w x from rfl]
      rw [show eLpNorm w 2 ((volume : Measure E).restrict Ω) =
          eLpNorm (Ω.indicator w) 2 (volume : Measure E) from
        (eLpNorm_indicator_eq_eLpNorm_restrict hΩ_open.measurableSet).symm]
    rw [h_eLpNorm_eq]
    exact hw_l2.eLpNorm_lt_top
  have h_dq_eq_on_tsupport : ∀ n : ℕ, ∀ x ∈ tsupport φ.1,
      diffQuot k (hₙ n) w_ext x = diffQuot k (hₙ n) w x := by
    intro n x hx
    have hx_Ω'' : x ∈ Ω'' := φ.2.2.2 hx
    have hx_closure_Ω'' : x ∈ closure Ω'' := subset_closure hx_Ω''
    have hx_in_Ω : x ∈ Ω := by
      have h1 : x ∈ Metric.cthickening h₀ (closure Ω'') :=
        Metric.self_subset_cthickening _ hx_closure_Ω''
      exact h_room h1
    have hx_he_in_Ω : x + (hₙ n) • EuclideanSpace.single k 1 ∈ Ω := by
      have h_dist : dist x (x + (hₙ n) • EuclideanSpace.single k 1) = |hₙ n| := by
        rw [dist_eq_norm]
        have heq : x - (x + (hₙ n) • EuclideanSpace.single k 1) =
            -((hₙ n) • EuclideanSpace.single k 1) := by abel
        rw [heq, norm_neg, norm_smul]
        rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
        rw [Real.norm_eq_abs, mul_one]
      have h_in_thick : x + (hₙ n) • EuclideanSpace.single k 1 ∈
          Metric.cthickening h₀ (closure Ω'') := by
        refine Metric.mem_cthickening_of_dist_le _ x h₀ (closure Ω'') hx_closure_Ω'' ?_
        rw [dist_comm]; rw [h_dist]; exact hₙ_bd n
      exact h_room h_in_thick
    have h_dq_apply : diffQuot k (hₙ n) w_ext x =
        (w_ext (x + (hₙ n) • EuclideanSpace.single k 1) - w_ext x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w_ext x]
    have h_dq_w_apply : diffQuot k (hₙ n) w x =
        (w (x + (hₙ n) • EuclideanSpace.single k 1) - w x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w x]
    rw [h_dq_apply, h_dq_w_apply]
    rw [hw_ext_eq_w_on_Ω _ hx_in_Ω, hw_ext_eq_w_on_Ω _ hx_he_in_Ω]
  have h_neg_h_int_eq_restrict : ∀ n,
      ∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) := by
    intro n
    have h_compl_zero : ∀ x ∉ Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x = 0 := by
      intro x hx
      rw [hw_ext_zero_off_Ω x hx, zero_mul]
    have h_split : ∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
          ∂(volume : Measure E) =
        ∫ x in Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
          ∂(volume : Measure E) := by
      symm
      rw [show (∫ x in Ω, w_ext x * diffQuot k (-(hₙ n)) φ.1 x
            ∂(volume : Measure E)) =
          ∫ x, Ω.indicator (fun y => w_ext y * diffQuot k (-(hₙ n)) φ.1 y) x
            ∂(volume : Measure E) from
        (integral_indicator hΩ_open.measurableSet).symm]
      refine integral_congr_ae ?_
      refine Filter.Eventually.of_forall ?_
      intro x
      by_cases hx : x ∈ Ω
      · rw [Set.indicator_of_mem hx]
      · rw [Set.indicator_of_notMem hx]
        exact (h_compl_zero x hx).symm
    rw [h_split]
    refine integral_congr_ae ?_
    have h_ae : ∀ᵐ x ∂((volume : Measure E).restrict Ω),
        w_ext x * diffQuot k (-(hₙ n)) φ.1 x = w x * diffQuot k (-(hₙ n)) φ.1 x := by
      rw [ae_restrict_iff' hΩ_open.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro x hx
      rw [hw_ext_eq_w_on_Ω x hx]
    exact h_ae
  have hIBP : ∀ n,
      ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        -∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E) := by
    intro n
    exact integral_diffQuot_mul_eq_neg_integral_mul_diffQuot
      (d := d) k (hₙ_ne n) hw_ext_memLp hφ_memLp_global
  have h_LHS_restrict : ∀ n,
      ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x
          ∂(volume : Measure E) := by
    intro n
    symm
    rw [show (∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x
          ∂(volume : Measure E)) =
        ∫ x, Ω''.indicator (fun y => diffQuot k (hₙ n) w_ext y * φ.1 y) x
          ∂(volume : Measure E) from
      (integral_indicator hΩ''_open.measurableSet).symm]
    refine integral_congr_ae ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    by_cases hx : x ∈ Ω''
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hxnot : x ∉ tsupport φ.1 := fun hxt => hx (φ.2.2.2 hxt)
      have hφx : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport hxnot
      change (0 : ℝ) = diffQuot k (hₙ n) w_ext x * φ.1 x
      rw [hφx, mul_zero]
  have h_LHS_on_tsupport : ∀ n,
      ∫ x in Ω'', diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x
          ∂(volume : Measure E) := by
    intro n
    refine integral_congr_ae ?_
    have h_ae : ∀ᵐ x ∂((volume : Measure E).restrict Ω''),
        diffQuot k (hₙ n) w_ext x * φ.1 x = diffQuot k (hₙ n) w x * φ.1 x := by
      rw [ae_restrict_iff' hΩ''_open.measurableSet]
      refine Filter.Eventually.of_forall ?_
      intro x _hx
      by_cases hxt : x ∈ tsupport φ.1
      · rw [h_dq_eq_on_tsupport n x hxt]
      · have hφx : φ.1 x = 0 := image_eq_zero_of_notMem_tsupport hxt
        rw [hφx, mul_zero, mul_zero]
    exact h_ae
  have h_dq_aesm_global : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w_ext)
      (volume : Measure E) :=
    fun n => aestronglyMeasurable_diffQuot (d := d) k _ hw_ext_memLp.aestronglyMeasurable
  have h_dq_aesm_restrict : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w_ext)
      ((volume : Measure E).restrict Ω'') :=
    fun n => (h_dq_aesm_global n).restrict
  have h_dq_eq_on_Ω'' : ∀ n : ℕ, ∀ x ∈ Ω'',
      diffQuot k (hₙ n) w_ext x = diffQuot k (hₙ n) w x := by
    intro n x hx_Ω''
    have hx_closure : x ∈ closure Ω'' := subset_closure hx_Ω''
    have hx_in_Ω : x ∈ Ω :=
      h_room (Metric.self_subset_cthickening _ hx_closure)
    have hx_he_in_Ω : x + (hₙ n) • EuclideanSpace.single k 1 ∈ Ω := by
      have h_dist : dist x (x + (hₙ n) • EuclideanSpace.single k 1) = |hₙ n| := by
        rw [dist_eq_norm]
        have heq : x - (x + (hₙ n) • EuclideanSpace.single k 1) =
            -((hₙ n) • EuclideanSpace.single k 1) := by abel
        rw [heq, norm_neg, norm_smul]
        rw [show ‖(EuclideanSpace.single k (1 : ℝ) : E)‖ = 1 by simp]
        rw [Real.norm_eq_abs, mul_one]
      have h_in_thick : x + (hₙ n) • EuclideanSpace.single k 1 ∈
          Metric.cthickening h₀ (closure Ω'') := by
        refine Metric.mem_cthickening_of_dist_le _ x h₀ (closure Ω'') hx_closure ?_
        rw [dist_comm]; rw [h_dist]; exact hₙ_bd n
      exact h_room h_in_thick
    have h_dq_apply : diffQuot k (hₙ n) w_ext x =
        (w_ext (x + (hₙ n) • EuclideanSpace.single k 1) - w_ext x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w_ext x]
    have h_dq_w_apply : diffQuot k (hₙ n) w x =
        (w (x + (hₙ n) • EuclideanSpace.single k 1) - w x) / (hₙ n) := by
      rw [diffQuot_apply_of_ne (d := d) k (hₙ_ne n) w x]
    rw [h_dq_apply, h_dq_w_apply]
    rw [hw_ext_eq_w_on_Ω _ hx_in_Ω, hw_ext_eq_w_on_Ω _ hx_he_in_Ω]
  have h_dq_ae_eq_restrict : ∀ n, diffQuot k (hₙ n) w_ext =ᵐ[
        (volume : Measure E).restrict Ω''] diffQuot k (hₙ n) w := by
    intro n
    rw [Filter.EventuallyEq, ae_restrict_iff' hΩ''_open.measurableSet]
    refine Filter.Eventually.of_forall ?_
    intro x hx
    exact h_dq_eq_on_Ω'' n x hx
  have h_dq_aesm_restrict_w : ∀ n, AEStronglyMeasurable (diffQuot k (hₙ n) w)
      ((volume : Measure E).restrict Ω'') := fun n =>
    (h_dq_aesm_restrict n).congr (h_dq_ae_eq_restrict n)
  have h_dq_memLp_restrict_w : ∀ n, MemLp (diffQuot k (hₙ n) w) 2
      ((volume : Measure E).restrict Ω'') := fun n =>
    ⟨h_dq_aesm_restrict_w n, lt_of_le_of_lt (h_dq_l2_bound n) ENNReal.ofReal_lt_top⟩
  have h_CS_bound : ∀ n,
      |∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    have h_cs := abs_integral_mul_le_norm_lp_mul_norm_lp_loc
      (μ := (volume : Measure E).restrict Ω'') (h_dq_memLp_restrict_w n) hφ_memLp
    have h_dq_bound :
        (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal
          ≤ M := by
      have hMto : (ENNReal.ofReal M).toReal = M := ENNReal.toReal_ofReal hM_nn
      calc (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal
          ≤ (ENNReal.ofReal M).toReal := by
            refine ENNReal.toReal_mono ENNReal.ofReal_ne_top ?_
            exact h_dq_l2_bound n
        _ = M := hMto
    have h_phi_nn : 0 ≤ (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal :=
      ENNReal.toReal_nonneg
    have hMul :
        (eLpNorm (diffQuot k (hₙ n) w) 2 ((volume : Measure E).restrict Ω'')).toReal *
            (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal ≤
          M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal :=
      mul_le_mul_of_nonneg_right h_dq_bound h_phi_nn
    have h_int_eq :
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E) =
          ∫ x, diffQuot k (hₙ n) w x * φ.1 x ∂((volume : Measure E).restrict Ω'') :=
      rfl
    rw [h_int_eq]
    linarith
  have h_dual_bound : ∀ n,
      |∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    have h_IBP_n := hIBP n
    have h_LHS_eq : ∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E) =
        ∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E) := by
      rw [h_LHS_restrict n, h_LHS_on_tsupport n]
    have h_LHS_abs : |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| =
        |∫ x in Ω'', diffQuot k (hₙ n) w x * φ.1 x ∂(volume : Measure E)| := by
      rw [h_LHS_eq]
    have h_LHS_le_bound :
        |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| ≤
          M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
      rw [h_LHS_abs]; exact h_CS_bound n
    have h_RHS_eq_LHS : |∫ x, w_ext x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| =
        |∫ x, diffQuot k (hₙ n) w_ext x * φ.1 x ∂(volume : Measure E)| := by
      rw [h_IBP_n, abs_neg]
    rw [h_RHS_eq_LHS]
    exact h_LHS_le_bound
  have h_dual_bound_restrict : ∀ n,
      |∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)| ≤
        M * (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    intro n
    rw [← h_neg_h_int_eq_restrict n]
    exact h_dual_bound n
  have h_abs_conv :
      Tendsto (fun n =>
          |∫ x in Ω, w x * diffQuot k (-(hₙ n)) φ.1 x ∂(volume : Measure E)|)
        atTop
        (𝓝 |∫ x in Ω, w x * (fderiv ℝ φ.1 x) (EuclideanSpace.single k 1)
          ∂(volume : Measure E)|) := by
    have := h_conv.abs
    simpa using this
  exact le_of_tendsto_of_tendsto'
    h_abs_conv tendsto_const_nhds (fun n => h_dual_bound_restrict n)

omit [NeZero d] in
lemma abs_smoothTestFunctional_loc_le_lpNorm
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCSSupportedInSubmodule (d := d) Ω'') :
    |smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ| ≤
      M * ‖smoothCSSupportedInToLp (d := d) Ω'' φ‖ := by
  have h := abs_smoothTestFunctional_loc_le (d := d) hΩ_open hΩ''_open
    hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd φ
  have h_norm_eq :
      ‖smoothCSSupportedInToLp (d := d) Ω'' φ‖ =
        (eLpNorm φ.1 2 ((volume : Measure E).restrict Ω'')).toReal := by
    rw [show (smoothCSSupportedInToLp (d := d) Ω'' φ :
        Lp ℝ 2 ((volume : Measure E).restrict Ω'')) =
      (memLp_two_restrict_of_smoothCS (d := d) (Ω'' := Ω'') φ.2.1 φ.2.2.1).toLp
        φ.1 from rfl]
    exact Lp.norm_toLp _ _
  rw [h_norm_eq]
  exact h

def smoothTestFunctionalLocExt
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    Lp ℝ 2 ((volume : Measure E).restrict Ω'') →L[ℝ] ℝ :=
  (smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k).extendOfNorm
    (smoothCSSupportedInToLp (d := d) Ω'')

omit [NeZero d] in
lemma opNorm_smoothTestFunctional_loc_ext_le
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M) :
    ‖smoothTestFunctionalLocExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ ≤ M := by
  unfold smoothTestFunctionalLocExt
  refine LinearMap.opNorm_extendOfNorm_le
    (denseRange_smoothCSSupportedInToLp (d := d) hΩ''_open hΩ''_compact_closure)
    hM_nn ?_
  intro φ
  exact abs_smoothTestFunctional_loc_le_lpNorm (d := d) hΩ_open hΩ''_open
    hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd φ

omit [NeZero d] in
lemma smoothTestFunctional_loc_ext_apply
    {Ω : Set E} (hΩ_open : IsOpen Ω)
    {Ω'' : Set E} (hΩ''_open : IsOpen Ω'')
    (hΩ''_compact_closure : IsCompact (closure Ω''))
    {h₀ : ℝ} (hh₀ : 0 < h₀)
    (h_room : Metric.cthickening h₀ (closure Ω'') ⊆ Ω)
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) {M : ℝ} (hM_nn : 0 ≤ M)
    (h_bdd : ∀ h : ℝ, 0 < |h| → |h| ≤ h₀ →
      eLpNorm (diffQuot k h w) 2 ((volume : Measure E).restrict Ω'')
        ≤ ENNReal.ofReal M)
    (φ : smoothCSSupportedInSubmodule (d := d) Ω'') :
    smoothTestFunctionalLocExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k
        (smoothCSSupportedInToLp (d := d) Ω'' φ) =
      smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ := by
  unfold smoothTestFunctionalLocExt
  refine LinearMap.extendOfNorm_eq
    (denseRange_smoothCSSupportedInToLp (d := d) hΩ''_open hΩ''_compact_closure)
    ⟨M, ?_⟩ φ
  intro ψ
  exact abs_smoothTestFunctional_loc_le_lpNorm (d := d) hΩ_open hΩ''_open
    hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd ψ

def smoothTestFunctionalLocRiesz
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    Lp ℝ 2 ((volume : Measure E).restrict Ω'') :=
  (InnerProductSpace.toDual ℝ
      (Lp ℝ 2 ((volume : Measure E).restrict Ω''))).symm
    (smoothTestFunctionalLocExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k)

omit [NeZero d] in
lemma norm_smoothTestFunctional_loc_riesz
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d) :
    ‖smoothTestFunctionalLocRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ =
      ‖smoothTestFunctionalLocExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k‖ := by
  unfold smoothTestFunctionalLocRiesz
  exact (InnerProductSpace.toDual ℝ
    (Lp ℝ 2 ((volume : Measure E).restrict Ω''))).symm.norm_map _

omit [NeZero d] in
lemma smoothTestFunctional_loc_ext_eq_inner
    {Ω Ω'' : Set E}
    {w : E → ℝ}
    (hw_l2 : MemLp w 2 ((volume : Measure E).restrict Ω))
    (k : Fin d)
    (f : Lp ℝ 2 ((volume : Measure E).restrict Ω'')) :
    smoothTestFunctionalLocExt (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k f =
      ⟪smoothTestFunctionalLocRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k, f⟫_ℝ := by
  unfold smoothTestFunctionalLocRiesz
  rw [InnerProductSpace.toDual_symm_apply]

end Poincare.Analysis.Sobolev
