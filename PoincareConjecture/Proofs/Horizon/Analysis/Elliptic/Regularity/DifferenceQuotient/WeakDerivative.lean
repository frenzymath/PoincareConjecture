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

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.LocalFunctional

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace
  RealInnerProductSpace

namespace Poincare.Analysis.Sobolev

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem hasWeakPartialDeriv_of_diffQuot_uniform_bound_loc
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
    ∃ g : E → ℝ,
      MemLp g 2 ((volume : Measure E).restrict Ω'') ∧
      (∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
        tsupport φ ⊆ Ω'' →
        (∫ x in Ω'', w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)) =
          -(∫ x in Ω'', g x * φ x)) ∧
      eLpNorm g 2 ((volume : Measure E).restrict Ω'') ≤ ENNReal.ofReal M := by
  have hΩ''_in_Ω : closure Ω'' ⊆ Ω :=
    (Metric.self_subset_cthickening (δ := h₀) (closure Ω'')).trans h_room
  set g_lp : Lp ℝ 2 ((volume : Measure E).restrict Ω'') :=
    smoothTestFunctionalLocRiesz (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k with hg_lp_def
  refine ⟨⇑g_lp, ?_, ?_, ?_⟩
  · exact Lp.memLp g_lp
  · intro φ hφ_smooth hφ_supp hφ_supp_in
    set φ_cs : smoothCSSupportedInSubmodule (d := d) Ω'' :=
      ⟨φ, hφ_smooth, hφ_supp, hφ_supp_in⟩ with hφ_cs_def
    have h_ext_apply :=
      smoothTestFunctional_loc_ext_apply (d := d) hΩ_open hΩ''_open
        hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd φ_cs
    have h_ext_inner :=
      smoothTestFunctional_loc_ext_eq_inner (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k
        (smoothCSSupportedInToLp (d := d) Ω'' φ_cs)
    have h_func_val :
        smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ_cs =
          -∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      rw [smoothTestFunctional_loc_apply]
    have h_inner_def := L2.inner_def (𝕜 := ℝ) g_lp
      (smoothCSSupportedInToLp (d := d) Ω'' φ_cs)
    have h_coeFn_phi :
        ⇑(smoothCSSupportedInToLp (d := d) Ω'' φ_cs) =ᵐ[
          (volume : Measure E).restrict Ω''] φ := by
      simp only [smoothCSSupportedInToLp_apply]
      exact MemLp.coeFn_toLp _
    have h_int_eq :
        ∫ x, ⟪g_lp x, (smoothCSSupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ
          ∂((volume : Measure E).restrict Ω'') =
          ∫ x in Ω'', g_lp x * φ x ∂(volume : Measure E) := by
      have h_eq : ∫ x, ⟪g_lp x,
            (smoothCSSupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ
          ∂((volume : Measure E).restrict Ω'') =
          ∫ x, g_lp x * φ x ∂((volume : Measure E).restrict Ω'') := by
        refine integral_congr_ae ?_
        filter_upwards [h_coeFn_phi] with x hx
        have h_inner_eq :
            ⟪(g_lp x : ℝ), (smoothCSSupportedInToLp (d := d) Ω'' φ_cs) x⟫_ℝ =
              (smoothCSSupportedInToLp (d := d) Ω'' φ_cs) x * (g_lp x : ℝ) :=
          RCLike.inner_apply (𝕜 := ℝ) (g_lp x)
            ((smoothCSSupportedInToLp (d := d) Ω'' φ_cs) x)
        rw [h_inner_eq, hx]; ring
      rw [h_eq]
    have h_chain :
        smoothTestFunctionalLoc (d := d) (Ω := Ω) (Ω'' := Ω'') hw_l2 k φ_cs =
          ∫ x in Ω'', g_lp x * φ x ∂(volume : Measure E) := by
      rw [← h_ext_apply, h_ext_inner, h_inner_def, h_int_eq]
    rw [h_func_val] at h_chain
    have h_int_Ω_eq_Ω'' :
        ∫ x in Ω, w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) =
          ∫ x in Ω'', w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
            ∂(volume : Measure E) := by
      have h_partial_zero_off_Ω'' : ∀ x ∉ Ω'',
          (fderiv ℝ φ x) (EuclideanSpace.single k 1) = 0 := by
        intro x hx
        have hxnot : x ∉ tsupport φ := fun hxt => hx (hφ_supp_in hxt)
        have h_eq_zero : φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
          have h_open := isClosed_tsupport φ |>.isOpen_compl
          have h_nhd := h_open.mem_nhds hxnot
          filter_upwards [h_nhd] with y hy
          have hy_supp : y ∉ Function.support φ := fun hy_in_supp =>
            hy (subset_tsupport _ hy_in_supp)
          rwa [Function.mem_support, not_not] at hy_supp
        have h_fderiv_eq : fderiv ℝ φ x = fderiv ℝ (fun _ : E => (0 : ℝ)) x :=
          h_eq_zero.fderiv_eq
        rw [h_fderiv_eq]
        simp
      have h_split : ∫ x in Ω,
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) =
          ∫ x in Ω'',
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
              ∂(volume : Measure E) := by
        have h_zero_on_diff : ∀ x ∉ Ω'',
            w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1) = 0 := by
          intro x hx
          rw [h_partial_zero_off_Ω'' x hx, mul_zero]
        have h_int_E_Ω : ∫ x in Ω,
              w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
                ∂(volume : Measure E) =
            ∫ x, Ω.indicator (fun y => w y *
                (fderiv ℝ φ y) (EuclideanSpace.single k 1)) x
              ∂(volume : Measure E) :=
          (integral_indicator hΩ_open.measurableSet).symm
        have h_int_E_Ω'' : ∫ x in Ω'',
              w x * (fderiv ℝ φ x) (EuclideanSpace.single k 1)
                ∂(volume : Measure E) =
            ∫ x, Ω''.indicator (fun y => w y *
                (fderiv ℝ φ y) (EuclideanSpace.single k 1)) x
              ∂(volume : Measure E) :=
          (integral_indicator hΩ''_open.measurableSet).symm
        rw [h_int_E_Ω, h_int_E_Ω'']
        refine integral_congr_ae ?_
        refine Filter.Eventually.of_forall ?_
        intro x
        by_cases hx_Ω'' : x ∈ Ω''
        · have hx_Ω : x ∈ Ω := hΩ''_in_Ω (subset_closure hx_Ω'')
          rw [Set.indicator_of_mem hx_Ω, Set.indicator_of_mem hx_Ω'']
        · rw [Set.indicator_of_notMem hx_Ω'']
          by_cases hx_Ω : x ∈ Ω
          · rw [Set.indicator_of_mem hx_Ω]
            exact h_zero_on_diff x hx_Ω''
          · rw [Set.indicator_of_notMem hx_Ω]
      exact h_split
    rw [h_int_Ω_eq_Ω''] at h_chain
    linarith
  · have h_norm_eq := norm_smoothTestFunctional_loc_riesz (d := d) (Ω := Ω)
      (Ω'' := Ω'') hw_l2 k
    have h_op_le := opNorm_smoothTestFunctional_loc_ext_le (d := d) hΩ_open
      hΩ''_open hΩ''_compact_closure hh₀ h_room hw_l2 k hM_nn h_bdd
    have h_g_lp_le : ‖g_lp‖ ≤ M := by
      rw [hg_lp_def]
      rw [h_norm_eq]
      exact h_op_le
    have h_g_lp_nn : 0 ≤ ‖g_lp‖ := norm_nonneg _
    have h_enorm_le : (‖g_lp‖ₑ : ℝ≥0∞) ≤ ENNReal.ofReal M := by
      have hofreal : (‖g_lp‖ₑ : ℝ≥0∞) = ENNReal.ofReal ‖g_lp‖ :=
        (ofReal_norm _).symm
      rw [hofreal]
      exact ENNReal.ofReal_le_ofReal h_g_lp_le
    have h_enorm_eq : ‖g_lp‖ₑ =
        eLpNorm (⇑g_lp) 2 ((volume : Measure E).restrict Ω'') :=
      Lp.enorm_def g_lp
    rw [← h_enorm_eq]
    exact h_enorm_le

end Poincare.Analysis.Sobolev
