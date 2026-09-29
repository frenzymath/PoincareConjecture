/-
Provenance and modification notice (recorded 2026-09-29).
Notices for the adapted portions:
Copyright 2026 The DifferentialGeometry contributors
Source: https://github.com/qinz1yang/differential-geometry
DifferentialGeometry/Analysis/Sobolev/Nirenberg/MasterInequality/CrossBounds.lean
Comparison revision: 1b535dd102b94cc42b107cca27059687888f08b3.
Modifications: Imports, module paths, and namespaces were adapted to this PoincareConjecture
development.
License: Apache-2.0; see LICENSES/Apache-2.0.txt and NOTICE.
See MODIFICATIONS.md for the reviewed file mapping and scope of this notice.
-/

import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Smooth.Coercivity
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Smooth.DifferenceQuotient
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Smooth.Integrability
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Smooth.Pointwise

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.NirenbergTestFunction
open Poincare.Analysis.Sobolev.NirenbergSubstitution
open Poincare.Analysis.Sobolev.NirenbergCoercivity
open scoped ENNReal NNReal Convolution Pointwise BigOperators InnerProductSpace

namespace Poincare.Analysis.Sobolev.NirenbergCrossBounds

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private lemma integral_const_indicator_eq
    {u : E → ℝ} (k : Fin d) (h : ℝ) (η : E → ℝ) (c : ℝ) :
    ∫ x, c * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 ∂(volume : Measure E) =
      c * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by
  have h_eq : (fun x : E => c *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2) =
      (fun x : E => c * ((Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2)) := by
    funext x; ring
  rw [h_eq, integral_const_mul]
  congr 1
  rw [show (fun x : E => (Set.indicator (tsupport η)
        (fun _ : E => (1 : ℝ)) x) * (diffQuot k h u x)^2) =
      (fun x : E => Set.indicator (tsupport η)
        (fun y : E => (diffQuot k h u y)^2) x) from by
    funext x
    by_cases hx : x ∈ tsupport η
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
  rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]

theorem translated_coeff_cutoff_deriv_diffQuot_cross_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω')
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            (Poincare.Analysis.Sobolev.translate k h
              (fun y : E => B.a y i j)) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
            Poincare.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨Λ, hΛ_nn, hΛ⟩ :=
    SmoothEllipticBilinearForm.bounded_a_on_compact (d := d) B hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (1 / (ε / d_real)) * Λ^2 * N^2 * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _)) (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    translated_coeff_cutoff_gradient_pointwise_bound (d := d) B hu hη hη_range h_fderiv_eta
      hΛ i j k h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        translate k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  have h_neg_abs : |- S| = |S| := abs_neg S
  rw [h_neg_abs]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x
        ∂(volume : Measure E)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine Finset.sum_le_sum ?_
    intro i _
    exact Finset.abs_sum_le_sum_abs _ _
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_1_summand (d := d) B hu hη hη_supp i j k hh
  have h_first_int : ∀ i : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    fun i => integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp
      i k hh (ε / d_real)
  have h_indicator_int : Integrable (fun x : E =>
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp
      k hh ((1 / (ε / d_real)) * Λ^2 * N^2)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i _ => (h_first_int i).add h_indicator_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
        (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
      (1 / (ε / d_real)) * Λ^2 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * translate k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
        diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          translate k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) +
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
          (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) +
        ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int i) h_indicator_int]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 +
        (1 / (ε / d_real)) * Λ^2 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_per_ij i j))]
    have h_step_b : ∀ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) := by
      intro i
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ _j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, d_real * (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_step_b i)]
    rw [← Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    rw [show (∑ _i : Fin d, ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        d_real * ∫ x, (1 / (ε / d_real)) * Λ^2 * N^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]]
    have h_indicator_eq := integral_const_indicator_eq (d := d) k h η
      ((1 / (ε / d_real)) * Λ^2 * N^2) (u := u)
    rw [h_indicator_eq]
    have h_eta_sq_diffQuot_int : ∀ i : Fin d,
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) =
        (ε / d_real) * ∫ x, (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (ε / d_real) * (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) =
          fun x : E => (ε / d_real) * ((η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
          from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E)) =
        ∑ i : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_eta_sq_diffQuot_int i)]
    rw [← Finset.mul_sum]
    have h_first_int_per : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
      fun i => integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp i k hh
    have h_swap_sum : ∑ i : Fin d, ∫ x, (η x)^2 *
            (diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) =
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
          ∂(volume : Measure E) := by
      rw [← integral_finsetSum _ (fun i _ => h_first_int_per i)]
      refine integral_congr_ae ?_
      filter_upwards with x
      rw [Finset.mul_sum]
    rw [h_swap_sum]
    rw [mul_add]
    congr 1
    · rw [← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    · ring
  rw [h_total_eq]
  have h_diffQuot_sq_le := integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d)
    hu k hh η hΩ' hΩ'_compact h_thick_in_Ω'
  unfold gradL2sqOn at h_diffQuot_sq_le
  have h_factor_nn : 0 ≤ (1 / (ε / d_real)) * Λ^2 * N^2 := by
    refine mul_nonneg (mul_nonneg ?_ (sq_nonneg _)) (sq_nonneg _)
    exact (one_div_pos.mpr hε'_pos).le
  have h_d_real_sq_nn : 0 ≤ d_real^2 := sq_nonneg _
  have h_C_eq : C = d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2) := by
    rw [hC_def]; ring
  have h_combine :
      d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    rw [show d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
        (d_real^2 * ((1 / (ε / d_real)) * Λ^2 * N^2)) *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)
        from by ring, ← h_C_eq]
    refine mul_le_mul_of_nonneg_left h_diffQuot_sq_le ?_
    rw [h_C_eq]; exact mul_nonneg h_d_real_sq_nn h_factor_nn
  linarith

theorem coeff_diffQuot_cutoff_sq_gradient_cross_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {Ω' : Set E} (hΩ' : IsOpen Ω')
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x *
            (η x)^2 *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
          ∂(volume : Measure E)| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨M, hM_nn, h_M⟩ :=
    SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  have hε'_pos : 0 < ε / d_real := div_pos hε hd_pos
  set C : ℝ := (M^2 / (4 * (ε / d_real))) * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg (sq_nonneg _) ?_
    refine inv_nonneg.mpr (by linarith [hε'_pos])
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    diffQuot_coeff_cutoff_squared_pointwise_bound (d := d) (u := u) B hη_range i j k hM_nn h_M
      h_thick_in_Ω' hε'_pos x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x,
        diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y : E => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
      volume :=
    fun i j => integrable_cross_2_summand (d := d) B hu hη hη_supp i j k hh
  have h_first_int : ∀ j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) volume :=
    fun j => integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp
      j k hh (ε / d_real)
  have h_second_int : ∀ i : Fin d, Integrable (fun x : E =>
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume :=
    fun i => integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i
      (M^2 / (4 * (ε / d_real)))
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      (ε / d_real) * (η x)^2 *
        (diffQuot k h
          (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
      (M^2 / (4 * (ε / d_real))) * (η x)^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume :=
    fun i j => (h_first_int j).add (h_second_int i)
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| ≤
      ∫ x, ((ε / d_real) * (η x)^2 *
          (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
        (M^2 / (4 * (ε / d_real))) * (η x)^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x,
          diffQuot k h (fun y => B.a y i j) x * (η x)^2 *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
        ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_eq :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) =
      ε * ∫ x, (η x)^2 *
          ∑ j : Fin d, (diffQuot k h
            (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
        ∂(volume : Measure E) +
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E)) := by
    have h_per_ij : ∀ i j : Fin d,
        ∫ x, ((ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
          (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) =
        ∫ x, (ε / d_real) * (η x)^2 *
            (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
          ∂(volume : Measure E) +
        ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_first_int j) (h_second_int i)]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          ∫ x, ((ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 +
            (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from
          Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_per_ij i j))]
    have h_inner_step : ∀ i : Fin d, ∑ j : Fin d,
          (∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) +
          ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) +
        d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
            (∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h
                  (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
              ∂(volume : Measure E) +
            ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
        ∑ i : Fin d,
          ((∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
                (diffQuot k h
                  (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
              ∂(volume : Measure E)) +
          d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => h_inner_step i)]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have h_first_eq : d_real * (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
        ε * ∫ x, (η x)^2 *
            ∑ j : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
          ∂(volume : Measure E) := by
      have h_pull_const : ∀ j : Fin d,
          ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) =
          (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) := by
        intro j
        rw [show (fun x : E => (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) =
            fun x : E => (ε / d_real) * ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) from
            by funext x; ring]
        rw [integral_const_mul]
      rw [show (∑ j : Fin d, ∫ x, (ε / d_real) * (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
          ∑ j : Fin d, (ε / d_real) * ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E) from
          Finset.sum_congr rfl (fun j _ => h_pull_const j)]
      rw [← Finset.mul_sum]
      have h_eta_sq_diffQuot_int : ∀ j : Fin d, Integrable (fun x : E =>
          (η x)^2 * (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2) volume :=
        fun j => integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp j k hh
      rw [show (∑ j : Fin d, ∫ x, (η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2
            ∂(volume : Measure E)) =
          ∫ x, ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2)
            ∂(volume : Measure E)
          from (integral_finsetSum _ (fun j _ => h_eta_sq_diffQuot_int j)).symm]
      have h_swap : (fun x : E => ∑ j : Fin d, ((η x)^2 *
              (diffQuot k h
                (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2)) =
          fun x : E => (η x)^2 * ∑ j : Fin d, (diffQuot k h
              (fun y => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x)^2 := by
        funext x; rw [Finset.mul_sum]
      rw [h_swap, ← mul_assoc, mul_div_cancel₀ _ (ne_of_gt hd_pos)]
    rw [h_first_eq]
    have h_second_eq :
        (∑ i : Fin d, d_real * ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        d_real * (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) :=
      (Finset.mul_sum _ _ _).symm
    rw [h_second_eq]
    have h_pull_const_2 : ∀ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) =
        (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          fun x : E => (M^2 / (4 * (ε / d_real))) * ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) from by funext x; ring]
      rw [integral_const_mul]
    rw [show (∑ i : Fin d, ∫ x, (M^2 / (4 * (ε / d_real))) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, (M^2 / (4 * (ε / d_real))) * ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_pull_const_2 i)]
    rw [← Finset.mul_sum]
    have h_inner_int : ∀ i : Fin d, Integrable (fun x : E =>
        (η x)^2 * (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
      intro i
      have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
      have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          (fun x : E => (η x)^2 *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
        funext x; ring
      rw [h_eq] at h; exact h
    rw [show (∑ i : Fin d, ∫ x, (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∫ x, ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ∂(volume : Measure E) from
        (integral_finsetSum _ (fun i _ => h_inner_int i)).symm]
    have h_swap : (fun x : E => ∑ i : Fin d, ((η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) =
        fun x : E => (η x)^2 *
            ∑ i : Fin d, ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) := by
      funext x; rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro i _; ring
    rw [h_swap]
  rw [h_total_eq]
  have h_M_factor_nn : 0 ≤ M^2 / (4 * (ε / d_real)) := by
    refine div_nonneg (sq_nonneg _) (by linarith)
  have h_d_real_ge_one : 1 ≤ d_real := by
    rw [hd_real]
    have hd_natpos : 0 < Fintype.card (Fin d) := Fintype.card_pos
    exact_mod_cast hd_natpos
  have h_ind_bound :
      ∫ x, (η x)^2 *
        ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
      ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
        ∂(volume : Measure E) := by
    have h_pointwise : ∀ x : E,
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
        (Set.indicator Ω' (fun y : E => ∑ i : Fin d,
          ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2)) x := by
      intro x
      by_cases hx : x ∈ tsupport η
      · have hx_Ω' : x ∈ Ω' :=
          h_thick_in_Ω' (self_subset_cthickening _ hx)
        rw [Set.indicator_of_mem hx_Ω']
        have h_η_in : η x ∈ Set.Icc (0 : ℝ) 1 := hη_range ⟨x, rfl⟩
        have h_η_sq_le : (η x)^2 ≤ 1 := by
          have h_η_le : η x ≤ 1 := h_η_in.2
          have h_η_nn : 0 ≤ η x := h_η_in.1
          calc (η x)^2 ≤ (1 : ℝ)^2 := by
                  refine pow_le_pow_left₀ h_η_nn h_η_le 2
            _ = 1 := one_pow _
        have h_η_sq_nn : 0 ≤ (η x)^2 := sq_nonneg _
        have h_indicator_le_one : ∀ y : E,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) y) ≤ 1 := by
          intro y
          by_cases hy : y ∈ tsupport η
          · rw [Set.indicator_of_mem hy]
          · rw [Set.indicator_of_notMem hy]; norm_num
        have h_sum_le : ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
          refine Finset.sum_le_sum ?_
          intro i _
          have h_le := h_indicator_le_one x
          have h_sq_nn : 0 ≤ ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := sq_nonneg _
          have h_step : (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ≤
              1 * ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 :=
            mul_le_mul_of_nonneg_right h_le h_sq_nn
          linarith
        have h_sum_nn : 0 ≤ ∑ i : Fin d,
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by
          refine Finset.sum_nonneg ?_
          intro i _
          have h_ind_nn : 0 ≤ Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x := by
            by_cases hxx : x ∈ tsupport η
            · rw [Set.indicator_of_mem hxx]; norm_num
            · rw [Set.indicator_of_notMem hxx]
          exact mul_nonneg h_ind_nn (sq_nonneg _)
        calc (η x)^2 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) ≤
            1 * (∑ i : Fin d,
                (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                  ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
              mul_le_mul_of_nonneg_right h_η_sq_le h_sum_nn
          _ = ∑ i : Fin d,
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
                ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := by ring
          _ ≤ ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 := h_sum_le
      · have h_η_zero : η x = 0 := image_eq_zero_of_notMem_tsupport hx
        rw [h_η_zero]
        simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, ge_iff_le]
        by_cases hx_Ω' : x ∈ Ω'
        · rw [Set.indicator_of_mem hx_Ω']
          exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
        · rw [Set.indicator_of_notMem hx_Ω']
    have h_lhs_int : Integrable (fun x : E =>
        (η x)^2 * ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
      have h_each_int : ∀ i : Fin d, Integrable (fun x : E =>
          (η x)^2 * ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) volume := by
        intro i
        have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
        have h_eq : (fun x : E => (1 : ℝ) * (η x)^2 *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
            (fun x : E => (η x)^2 *
              ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) := by
          funext x; ring
        rw [h_eq] at h; exact h
      have h_sum_int : Integrable (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) volume :=
        integrable_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => h_each_int i)
      have h_eq : (fun x : E => ∑ i : Fin d, (η x)^2 *
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) =
          (fun x : E => (η x)^2 * ∑ i : Fin d,
            ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2)) := by
        funext x; rw [Finset.mul_sum]
      rw [h_eq] at h_sum_int; exact h_sum_int
    have h_rhs_int : Integrable (fun y : E =>
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) y) volume := by
      have h_partial_sq_cont : ∀ i : Fin d,
          Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
        fun i => (continuous_partial_u (d := d) hu i).pow 2
      have h_sum_cont : Continuous (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
        continuous_finsetSum _ (fun i _ => h_partial_sq_cont i)
      have h_int_clΩ' : IntegrableOn (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (closure Ω') volume :=
        ContinuousOn.integrableOn_compact hΩ'_compact h_sum_cont.continuousOn
      have h_int_Ω' : IntegrableOn (fun x : E =>
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) Ω' volume :=
        h_int_clΩ'.mono_set subset_closure
      exact h_int_Ω'.integrable_indicator hΩ'.measurableSet
    have h_int_le := integral_mono h_lhs_int h_rhs_int h_pointwise
    refine h_int_le.trans ?_
    rw [show (fun y : E => Set.indicator Ω' (fun z : E => ∑ i : Fin d,
            ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) y) =
        Set.indicator Ω' (fun z : E => ∑ i : Fin d,
          ((fderiv ℝ u z) (EuclideanSpace.single i 1))^2) from rfl]
    rw [MeasureTheory.integral_indicator hΩ'.measurableSet]
  have h_combine :
      d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    have h_step1 : d_real * ((M^2 / (4 * (ε / d_real))) *
        ∫ x, (η x)^2 *
            ∑ i : Fin d, (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ hd_nn
      exact mul_le_mul_of_nonneg_left h_ind_bound h_M_factor_nn
    refine h_step1.trans ?_
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) := by
      refine integral_nonneg ?_
      intro x
      exact Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h_step2 :
        d_real * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) ≤
        d_real^2 * ((M^2 / (4 * (ε / d_real))) *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      have h_factor_nn :
          0 ≤ (M^2 / (4 * (ε / d_real))) *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_nonneg h_M_factor_nn h_J_nn
      have h_d_le_d_sq : d_real ≤ d_real^2 := by
        have h := h_d_real_ge_one
        nlinarith
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_factor_nn
    refine h_step2.trans ?_
    have h_C_eq : C = d_real^2 * (M^2 / (4 * (ε / d_real))) := by
      rw [hC_def]; ring
    rw [show d_real^2 * ((M^2 / (4 * (ε / d_real))) *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E)) =
      (d_real^2 * (M^2 / (4 * (ε / d_real)))) *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  linarith

theorem coeff_diffQuot_cutoff_deriv_cross_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω')
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
            Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => B.a y i j) x *
            (η x) *
            ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
            Poincare.Analysis.Sobolev.diffQuot k h u x
          ∂(volume : Measure E)| ≤
        C * ∫ x in Ω',
            ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
          ∂(volume : Measure E) := by
  classical
  obtain ⟨M, hM_nn, h_M⟩ :=
    SmoothEllipticBilinearForm.bounded_fderiv_a_on_compact (d := d) B k hΩ'_compact
  set d_real : ℝ := (Fintype.card (Fin d) : ℝ) with hd_real
  have hd_pos : 0 < d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_ge_one : 1 ≤ d_real := by
    rw [hd_real]; exact_mod_cast Fintype.card_pos
  have hd_nn : 0 ≤ d_real := hd_pos.le
  set C : ℝ := 2 * M * N * d_real^2 with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine mul_nonneg ?_ (sq_nonneg _)
    refine mul_nonneg ?_ hN
    exact mul_nonneg (by linarith) hM_nn
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  have h_each_pointwise := fun (i j : Fin d) (x : E) =>
    diffQuot_coeff_cutoff_gradient_pointwise_bound (d := d) B (u := u) hη_range h_fderiv_eta i j k
      hM_nn h_M
      h_thick_in_Ω' x
  set S : ℝ := ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
        diffQuot k h (fun y : E => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x
      ∂(volume : Measure E) with hS_def
  rw [abs_neg]
  have h_abs_sum : |S| ≤
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y : E => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| :=
    (Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum (fun i _ => Finset.abs_sum_le_sum_abs _ _))
  refine h_abs_sum.trans ?_
  have h_integrand_int : ∀ i j : Fin d, Integrable (fun x : E =>
      2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
        ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
        diffQuot k h u x) volume :=
    fun i j => integrable_cross_3_summand (d := d) B hu hη hη_supp i j k hh
  have h_pt_bound1_int : ∀ i : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) volume := by
    intro i
    have h := integrable_const_eta_sq_indicator_partial_sq (d := d) hu hη hη_supp i 1
    have h_partial_cont : Continuous
        (fun x : E => (fderiv ℝ u x) (EuclideanSpace.single i 1)) :=
      continuous_partial_u (d := d) hu i
    have h_partial_sq_cont : Continuous
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      h_partial_cont.pow 2
    have h_tsupp_meas : MeasurableSet (tsupport η) :=
      isClosed_tsupport η |>.measurableSet
    have h_tsupp_compact : IsCompact (tsupport η) := hη_supp
    have h_eq : (fun x : E => M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
        Set.indicator (tsupport η)
          (fun y : E => M * N * ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) := by
      funext x
      by_cases hx : x ∈ tsupport η
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring
    rw [h_eq]
    have h_inner_cont : Continuous (fun y : E =>
        M * N * ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) :=
      continuous_const.mul h_partial_sq_cont
    exact (ContinuousOn.integrableOn_compact h_tsupp_compact
      h_inner_cont.continuousOn).integrable_indicator
      h_tsupp_meas
  have h_pt_bound2_int : Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp k hh (M * N)
  have h_pt_bound_int : ∀ i j : Fin d, Integrable (fun x : E =>
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
      M * N *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    fun i j => (h_pt_bound1_int i).add h_pt_bound2_int
  have h_per_pair_bound : ∀ i j : Fin d,
      |∫ x, 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∫ x, (M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
        M * N *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2) ∂(volume : Measure E) := by
    intro i j
    have h_tri := abs_integral_le_integral_abs (μ := (volume : Measure E))
      (f := fun x : E => 2 * diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x)
    refine h_tri.trans ?_
    refine integral_mono_ae ((h_integrand_int i j).abs) (h_pt_bound_int i j) ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    exact h_each_pointwise i j x
  have h_outer_sum :
      ∑ i : Fin d, ∑ j : Fin d, |∫ x, 2 *
          diffQuot k h (fun y => B.a y i j) x * (η x) *
          ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
          ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
          diffQuot k h u x ∂(volume : Measure E)| ≤
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) :=
    Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => h_per_pair_bound i j))
  refine h_outer_sum.trans ?_
  have h_total_bound :
      ∑ i : Fin d, ∑ j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) ≤
      C * ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
        ∂(volume : Measure E) := by
    have h_split_integral : ∀ i j : Fin d,
        ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E) =
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      intro i j
      rw [integral_add (h_pt_bound1_int i) h_pt_bound2_int]
    have h_A_factor : ∀ i : Fin d,
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      rw [show (fun x : E => M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          fun x : E => M * N * ((Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) from by funext x; ring]
      rw [integral_const_mul]
      congr 1
      rw [show (fun x : E => (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) =
          (fun x : E => Set.indicator (tsupport η)
            (fun y : E => ((fderiv ℝ u y) (EuclideanSpace.single i 1))^2) x) from by
        funext x
        by_cases hx : x ∈ tsupport η
        · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]; ring
        · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]; ring]
      rw [MeasureTheory.integral_indicator (isClosed_tsupport η).measurableSet]
    have h_B_factor :
        ∫ x, M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2 ∂(volume : Measure E) =
        M * N * ∫ x in tsupport η,
          (diffQuot k h u x)^2 ∂(volume : Measure E) :=
      integral_const_indicator_eq (d := d) k h η (M * N) (u := u)
    rw [show (∑ i : Fin d, ∑ j : Fin d, ∫ x, (M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 +
          M * N *
            (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
            (diffQuot k h u x)^2) ∂(volume : Measure E)) =
        ∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from
        Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => h_split_integral i j))]
    rw [show (∑ i : Fin d, ∑ j : Fin d,
          (∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
          ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) +
        ∑ i : Fin d, (∑ j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) from by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [Finset.sum_add_distrib]]
    have h_step1 : (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
        d_real * ∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      rw [show (∑ i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E))) =
          ∑ i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul])]
      rw [← Finset.mul_sum]
    have h_step2 : (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
        d_real^2 * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
      have h_inner : ∀ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E)) =
            d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) := by
        intro _i
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [show (∑ _i : Fin d, (∑ _j : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E))) =
          ∑ _i : Fin d, d_real * ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              (diffQuot k h u x)^2 ∂(volume : Measure E) from
            Finset.sum_congr rfl (fun i _ => h_inner i)]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      rw [← mul_assoc, ← hd_real]
      ring
    rw [h_step1, h_step2]
    rw [show (∑ i : Fin d, ∫ x, M * N *
              (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
        ∑ i : Fin d, M * N * ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) from
        Finset.sum_congr rfl (fun i _ => h_A_factor i)]
    rw [h_B_factor]
    have h_MN_nn : 0 ≤ M * N := mul_nonneg hM_nn hN
    have h_d_le_d_sq : d_real ≤ d_real^2 := by nlinarith
    have h_J_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
      integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
    have h_partial_sq_cont : ∀ i : Fin d,
        Continuous (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) :=
      fun i => (continuous_partial_u (d := d) hu i).pow 2
    have h_int_clΩ' : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (closure Ω') volume :=
      fun i => ContinuousOn.integrableOn_compact hΩ'_compact (h_partial_sq_cont i).continuousOn
    have h_int_Ω' : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) Ω' volume :=
      fun i => (h_int_clΩ' i).mono_set subset_closure
    have h_tsupp_subset_Ω' : tsupport η ⊆ Ω' :=
      fun x hx => h_thick_in_Ω' (self_subset_cthickening _ hx)
    have h_int_tsupp : ∀ i : Fin d, IntegrableOn
        (fun x : E => ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2) (tsupport η) volume :=
      fun i => (h_int_Ω' i).mono_set h_tsupp_subset_Ω'
    have h_part_bound : ∀ i : Fin d,
        ∫ x in tsupport η, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      intro i
      refine setIntegral_mono_set (h_int_Ω' i) ?_ ?_
      · exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
      · exact Filter.Eventually.of_forall h_tsupp_subset_Ω'
    have h_sum_part_bound :
        ∑ i : Fin d, ∫ x in tsupport η,
          ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
      have h_sum_eq :
          ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) =
          ∑ i : Fin d, ∫ x in Ω',
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) := by
        exact integral_finsetSum (Finset.univ : Finset (Fin d)) (fun i _ => h_int_Ω' i)
      rw [h_sum_eq]
      exact Finset.sum_le_sum (fun i _ => h_part_bound i)
    have h_diff_bound :
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω',
          ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) :=
      integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
        hΩ'_compact h_thick_in_Ω'
    have h_term1 :
        d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      rw [show (d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) =
          (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) from by
        rw [← Finset.mul_sum]; ring]
      have h_step_a : (d_real * (M * N)) * (∑ i : Fin d, ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E)) ≤
          (d_real * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
        refine mul_le_mul_of_nonneg_left h_sum_part_bound ?_
        exact mul_nonneg hd_nn h_MN_nn
      refine h_step_a.trans ?_
      rw [show d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) =
          (d_real^2 * (M * N)) * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) from by ring]
      refine mul_le_mul_of_nonneg_right ?_ h_J_nn
      exact mul_le_mul_of_nonneg_right h_d_le_d_sq h_MN_nn
    have h_term2 :
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E)) := by
      refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left h_diff_bound h_MN_nn
    have h_sum_le : d_real * ∑ i : Fin d, M * N *
            ∫ x in tsupport η,
              ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2 ∂(volume : Measure E) +
        d_real^2 * (M * N * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) ≤
        2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E))) := by linarith
    refine h_sum_le.trans ?_
    have h_C_eq : C = 2 * d_real^2 * M * N := by
      rw [hC_def]; ring
    rw [show 2 * (d_real^2 * (M * N * ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E))) =
        (2 * d_real^2 * M * N) *
          ∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) from by ring]
    rw [← h_C_eq]
  exact h_total_bound

omit [NeZero d] in
private theorem nirenbergTestFunction_sq_integral_le
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    ∫ x, (Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u x)^2 ∂(volume : Measure E) ≤
      8 * N^2 *
        ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
      2 * ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) := by
  set g : E → ℝ := fun y : E => η y ^ 2 * diffQuot k h u y with hg_def
  have hg_smooth : ContDiff ℝ 1 g := by
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => η y ^ 2) := hη.pow 2
    have h2 : ContDiff ℝ (⊤ : ℕ∞) (Poincare.Analysis.Sobolev.diffQuot k h u) :=
      contDiff_diffQuot_of_contDiff (d := d) hu k hh
    exact (h1.mul h2).of_le (by norm_cast)
  have hg_supp : HasCompactSupport g := by
    have h_eta_sq_supp : HasCompactSupport (fun y : E => η y ^ 2) := by
      have heq : (fun y : E => η y ^ 2) = (fun y : E => η y * η y) := by
        funext y; ring
      rw [heq]; exact hη_supp.mul_right
    exact h_eta_sq_supp.mul_right
  have hnh : (-h) ≠ 0 := neg_ne_zero.mpr hh
  have h_thick_int : Integrable
      (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1)) ^ 2)
      ((volume : Measure E).restrict (Metric.cthickening |-h| (Set.univ : Set E))) := by
    have h_fderiv_g_cont : Continuous (fderiv ℝ g) :=
      hg_smooth.continuous_fderiv (by norm_num)
    have h_partial_cont : Continuous (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      h_fderiv_g_cont.clm_apply continuous_const
    have h_partial_sq_cont : Continuous
      (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) :=
      h_partial_cont.pow 2
    have h_partial_supp : HasCompactSupport
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) hg_supp (EuclideanSpace.single k 1)
    have h_partial_sq_supp : HasCompactSupport
        (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) := by
      have : (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) =
          (fun x : ℝ => x^2) ∘ (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) := by
        funext y; rfl
      rw [this]
      exact HasCompactSupport.comp_left h_partial_supp (by simp : (0 : ℝ)^2 = 0)
    exact (h_partial_sq_cont.integrable_of_hasCompactSupport h_partial_sq_supp).integrableOn
  have h_local := integral_sq_diffQuot_le_local (d := d) hg_smooth k hnh
    MeasurableSet.univ h_thick_int
  have h_v_test_eq : (fun x : E =>
      (Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
        k h η u x)^2) =
      fun x : E => (diffQuot k (-h) g x)^2 := by
    funext x
    unfold Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
    rfl
  rw [h_v_test_eq]
  have h_lhs : ∫ x, (diffQuot k (-h) g x)^2 ∂(volume : Measure E) ≤
      ∫ y, ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) := by
    have h_lhs_restrict : ∫ x in (Set.univ : Set E),
        (diffQuot k (-h) g x)^2 ∂(volume : Measure E) =
      ∫ x, (diffQuot k (-h) g x)^2 ∂(volume : Measure E) := by
      rw [Measure.restrict_univ]
    have h_rhs_restrict : ∫ y in Metric.cthickening |-h| (Set.univ : Set E),
        ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) =
      ∫ y, ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2 ∂(volume : Measure E) := by
      have h_eq : Metric.cthickening |-h| (Set.univ : Set E) = Set.univ := by
        ext y
        constructor
        · intro _; trivial
        · intro _
          exact Metric.self_subset_cthickening _ trivial
      rw [h_eq, Measure.restrict_univ]
    rw [← h_lhs_restrict, ← h_rhs_restrict]
    exact h_local
  refine h_lhs.trans ?_
  have h_pointwise_bound : ∀ x : E,
      ((fderiv ℝ g x) (EuclideanSpace.single k 1))^2 ≤
        8 * N^2 *
          (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
          (diffQuot k h u x)^2 +
        2 * (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 := by
    intro x
    exact fderiv_eta_sq_diffQuot_sq_bound (d := d) hu hη hη_range h_fderiv_eta k hh x
  have h_lhs_int : Integrable (fun x : E =>
      ((fderiv ℝ g x) (EuclideanSpace.single k 1))^2) volume := by
    have h_fderiv_g_cont : Continuous (fderiv ℝ g) :=
      hg_smooth.continuous_fderiv (by norm_num)
    have h_partial_cont : Continuous (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      h_fderiv_g_cont.clm_apply continuous_const
    have h_partial_sq_cont : Continuous
      (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) :=
      h_partial_cont.pow 2
    have h_partial_supp : HasCompactSupport
        (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) :=
      HasCompactSupport.fderiv_apply (𝕜 := ℝ) hg_supp (EuclideanSpace.single k 1)
    have h_partial_sq_supp : HasCompactSupport
        (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) := by
      have : (fun y : E => ((fderiv ℝ g y) (EuclideanSpace.single k 1))^2) =
          (fun x : ℝ => x^2) ∘ (fun y : E => (fderiv ℝ g y) (EuclideanSpace.single k 1)) := by
        funext y; rfl
      rw [this]
      exact HasCompactSupport.comp_left h_partial_supp (by simp : (0 : ℝ)^2 = 0)
    exact h_partial_sq_cont.integrable_of_hasCompactSupport h_partial_sq_supp
  have h_t1_int : Integrable (fun x : E =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2) volume :=
    integrable_const_indicator_diffQuot_sq (d := d) hu hη_supp k hh (8 * N^2)
  have h_t2_int : Integrable (fun x : E =>
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_const_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh 2
  have h_rhs_int : Integrable (fun x : E =>
      8 * N^2 *
        (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
        (diffQuot k h u x)^2 +
      2 * (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    h_t1_int.add h_t2_int
  have h_int_le := integral_mono h_lhs_int h_rhs_int h_pointwise_bound
  refine h_int_le.trans ?_
  rw [integral_add h_t1_int h_t2_int]
  have h_t1_eq : ∫ x, 8 * N^2 *
      (Set.indicator (tsupport η) (fun _ : E => (1 : ℝ)) x) *
      (diffQuot k h u x)^2 ∂(volume : Measure E) =
    8 * N^2 * ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) :=
    integral_const_indicator_eq (d := d) k h η (8 * N^2) (u := u)
  rw [h_t1_eq]
  have h_t2_eq : ∫ x, 2 * (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ∂(volume : Measure E) =
    2 * ∫ x, (η x)^2 *
      (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ∂(volume : Measure E) := by
    rw [show (fun x : E => 2 * (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) =
        fun x : E => 2 * ((η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) from by
        funext x; ring]
    rw [integral_const_mul]
  rw [h_t2_eq]

theorem c_term_bound
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, B.c x * u x *
          Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) := by
  classical
  obtain ⟨Mc, hMc_nn, h_Mc⟩ :=
    SmoothEllipticBilinearForm.bounded_c_on_compact (d := d) B hΩ'_compact
  set C : ℝ := max (4 * ε * N^2) (Mc^2 / (2 * ε)) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε.le
  refine ⟨C, hC_nn, ?_⟩
  intro u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  set v_test : E → ℝ :=
    Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u with hv_test_def
  have h_v_test_supp : tsupport v_test ⊆ Ω' := v_test_supported_in_Ω' hh_supp_in_Ω' k hh_le
  have h_v_test_in_Ω : tsupport v_test ⊆ Ω := fun x hx =>
    hΩ'_closure (subset_closure (h_v_test_supp hx))
  have h_v_test_cont : Continuous v_test := continuous_v_test (d := d) hu hη k hh
  have h_v_test_supp_cmp : HasCompactSupport v_test :=
    hasCompactSupport_v_test (d := d) hη_supp k h
  have h_c_cont : Continuous B.c := B.continuous_c
  have h_u_cont : Continuous u := hu.continuous
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_in_Ω hy))
  have h_int_E : ∫ x in Ω, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside x hx]; ring
    exact setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero
  rw [h_int_E]
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_supp hy))
  have h_int_Ω' : ∫ x, B.c x * u x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero : ∀ x, x ∉ Ω' → B.c x * u x * v_test x = 0 := by
      intro x hx
      rw [h_v_test_zero_outside_Ω' x hx]; ring
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
  rw [h_int_Ω']
  have h_pointwise_cu_v : ∀ x : E,
      |B.c x * u x * v_test x| ≤ (ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2 := by
    intro x
    have h_y := two_abs_mul_le_eps_sq_add (v_test x) (B.c x * u x) ε hε
    have h_abs_eq : |B.c x * u x * v_test x| = |v_test x| * |B.c x * u x| := by
      rw [show (B.c x * u x * v_test x) = v_test x * (B.c x * u x) from by ring,
        abs_mul]
    rw [h_abs_eq]
    have h_ε_pos_inv : (1 : ℝ) / ε > 0 := one_div_pos.mpr hε
    have h_div_eq : (1 / ε) * (B.c x * u x)^2 = 2 * ((1 / (2 * ε)) * (B.c x * u x)^2) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h_ε_eq : ε * (v_test x)^2 = 2 * ((ε / 2) * (v_test x)^2) := by ring
    linarith [h_y, h_div_eq, h_ε_eq]
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x)^2) Ω' volume := by
    have h_square_supp : HasCompactSupport (fun x : E => (v_test x) ^ 2) := by
      exact HasCompactSupport.intro' h_v_test_supp_cmp (isClosed_tsupport v_test)
        (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport hx]
          norm_num)
    have h_int : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        h_square_supp
    exact h_int.integrableOn
  have h_cu_sq_int_Ω' : IntegrableOn (fun x : E => (B.c x * u x)^2) Ω' volume := by
    have h_cont : Continuous (fun x : E => (B.c x * u x)^2) :=
      (h_c_cont.mul h_u_cont).pow 2
    have h_cont_on : ContinuousOn (fun x : E => (B.c x * u x)^2) (closure Ω') :=
      h_cont.continuousOn
    exact (ContinuousOn.integrableOn_compact hΩ'_compact h_cont_on).mono_set subset_closure
  have h_cu_v_int_Ω' : IntegrableOn (fun x : E => B.c x * u x * v_test x) Ω' volume := by
    have h_cont : Continuous (fun x : E => B.c x * u x * v_test x) :=
      (h_c_cont.mul h_u_cont).mul h_v_test_cont
    have h_supp : HasCompactSupport (fun x : E => B.c x * u x * v_test x) :=
      h_v_test_supp_cmp.mul_left
    exact (h_cont.integrable_of_hasCompactSupport h_supp).integrableOn
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', B.c x * u x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |B.c x * u x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω',
        ((ε/2) * (v_test x)^2 + (1/(2*ε)) * (B.c x * u x)^2)
        ∂(volume : Measure E) := by
    refine integral_mono_ae h_cu_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise_cu_v x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2)) (h_cu_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [show (fun x : E => (ε/2) * (v_test x)^2) =
      (fun x : E => (ε/2) * (v_test x)^2) from rfl]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x)^2 ∂(volume : Measure E) := by
    have h_square_supp : HasCompactSupport (fun x : E => (v_test x) ^ 2) := by
      exact HasCompactSupport.intro' h_v_test_supp_cmp (isClosed_tsupport v_test)
        (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport hx]
          norm_num)
    have h_int_E : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        h_square_supp
    have h_v_test_sq_eq : ∫ x, (v_test x)^2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x)^2 = 0 := by
        intro x hx
        rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_v_test_sq_eq]
  have h_v_test_bound := nirenbergTestFunction_sq_integral_le (d := d) hu hη hη_supp hη_range
    h_fderiv_eta k hh
  have h_cu_sq_bound : ∀ x ∈ Ω', (B.c x * u x)^2 ≤ Mc^2 * (u x)^2 := by
    intro x hx
    have h_x_in_clΩ' : x ∈ closure Ω' := subset_closure hx
    have h_c_le : |B.c x| ≤ Mc := h_Mc x h_x_in_clΩ'
    have h_c_sq_le : (B.c x)^2 ≤ Mc^2 := by
      rw [← sq_abs (B.c x)]; exact pow_le_pow_left₀ (abs_nonneg _) h_c_le 2
    have h_u_sq_nn : 0 ≤ (u x)^2 := sq_nonneg _
    calc (B.c x * u x)^2 = (B.c x)^2 * (u x)^2 := by ring
      _ ≤ Mc^2 * (u x)^2 := mul_le_mul_of_nonneg_right h_c_sq_le h_u_sq_nn
  have h_cu_sq_int_Ω'_le : ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
      Mc^2 * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
    have h_u_sq_int_Ω' : IntegrableOn (fun x : E => (u x)^2) Ω' volume := by
      have h_cont : Continuous (fun x : E => (u x)^2) := h_u_cont.pow 2
      have h_cont_on : ContinuousOn (fun x : E => (u x)^2) (closure Ω') := h_cont.continuousOn
      exact (ContinuousOn.integrableOn_compact hΩ'_compact h_cont_on).mono_set subset_closure
    have h_const_int : IntegrableOn (fun x : E => Mc^2 * (u x)^2) Ω' volume :=
      h_u_sq_int_Ω'.const_mul (Mc^2)
    have h_step : ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', Mc^2 * (u x)^2 ∂(volume : Measure E) :=
      setIntegral_mono_on h_cu_sq_int_Ω' h_const_int hΩ'.measurableSet h_cu_sq_bound
    rw [integral_const_mul] at h_step
    exact h_step
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
      hΩ'_compact h_thick_in_Ω'
  have h_partial_le_sum : ∀ x : E,
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ≤
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum (f := fun i => (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h_eta_sq_partial_int : Integrable (fun x : E =>
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh
  have h_eta_sq_sum_int : Integrable (fun x : E =>
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_sum (d := d) hu hη hη_supp k hh
  have h_partial_int_le :
      ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) :=
    integral_mono h_eta_sq_partial_int h_eta_sq_sum_int h_partial_le_sum
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_uL2_nn : 0 ≤ ∫ x in Ω', (u x)^2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      4 * ε * N^2 *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) +
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
          2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) ≤
        4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
          4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N^2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
          4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      have h_step_d : ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) ≤
          ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_partial_int_le hε.le
      linarith [h1, h2]
    linarith
  have h_cu_full_bound :
      (1/(2*ε)) * ∫ x in Ω', (B.c x * u x)^2 ∂(volume : Measure E) ≤
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
    have h_div_pos : 0 < 1/(2*ε) := by
      refine one_div_pos.mpr ?_; linarith
    have h_step := mul_le_mul_of_nonneg_left h_cu_sq_int_Ω'_le h_div_pos.le
    have h_eq : (1 / (2 * ε)) * (Mc ^ 2 * ∫ x in Ω', u x ^ 2 ∂(volume : Measure E)) =
        Mc^2 / (2*ε) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by
      ring
    linarith [h_step, h_eq]
  have h_C_grad_le : 4 * ε * N^2 ≤ C := le_max_left _ _
  have h_C_uL2_le : Mc^2 / (2*ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N^2 *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) +
      (Mc^2 / (2 * ε)) * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_uL2_le h_uL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E)) +
        C * ∫ x in Ω', (u x)^2 ∂(volume : Measure E) := by ring
    linarith
  linarith

omit [NeZero d] in
theorem f_term_bound
    {Ω : Set E}
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : E → ℝ}, (∀ {Ω' : Set E}, IsCompact (closure Ω') →
        MemLp f 2 (volume.restrict Ω')) →
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      |∫ x in Ω, f x *
          Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
            k h η u x| ≤
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  set C : ℝ := max (4 * ε * N^2) (1 / (2 * ε)) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine mul_nonneg ?_ (sq_nonneg _)
    exact mul_nonneg (by linarith) hε.le
  refine ⟨C, hC_nn, ?_⟩
  intro f hf_l2_loc u hu h hh hh_le
  have h_thick_in_Ω' : Metric.cthickening |h| (tsupport η) ⊆ Ω' := hh_supp_in_Ω' hh_le
  set v_test : E → ℝ :=
    Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
      k h η u with hv_test_def
  have h_v_test_supp : tsupport v_test ⊆ Ω' := v_test_supported_in_Ω' hh_supp_in_Ω' k hh_le
  have h_v_test_cont : Continuous v_test := continuous_v_test (d := d) hu hη k hh
  have h_v_test_supp_cmp : HasCompactSupport v_test :=
    hasCompactSupport_v_test (d := d) hη_supp k h
  have h_v_test_zero_outside : ∀ x ∉ Ω, v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport
      (fun hy => hx (hΩ'_closure (subset_closure (h_v_test_supp hy))))
  have h_v_test_zero_outside_Ω' : ∀ x ∉ Ω', v_test x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun hy => hx (h_v_test_supp hy))
  have hf_memLp : MemLp f 2 (volume.restrict Ω') := hf_l2_loc hΩ'_compact
  have hf_sq_int_Ω' : IntegrableOn (fun x : E => (f x)^2) Ω' volume := hf_memLp.integrable_sq
  have h_int_E : ∫ x in Ω, f x * v_test x ∂(volume : Measure E) =
      ∫ x in Ω', f x * v_test x ∂(volume : Measure E) := by
    have h_eq_zero_Ω : ∀ x, x ∉ Ω → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside x hx]; ring
    have h_eq_zero_Ω' : ∀ x, x ∉ Ω' → f x * v_test x = 0 := by
      intro x hx; rw [h_v_test_zero_outside_Ω' x hx]; ring
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω,
      ← setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero_Ω']
  rw [h_int_E]
  have h_pointwise : ∀ x : E,
      |f x * v_test x| ≤ (ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2 := by
    intro x
    have h_y := two_abs_mul_le_eps_sq_add (v_test x) (f x) ε hε
    have h_abs_eq : |f x * v_test x| = |v_test x| * |f x| := by
      rw [show (f x * v_test x) = v_test x * f x from by ring, abs_mul]
    rw [h_abs_eq]
    have h_div_eq : (1 / ε) * (f x)^2 = 2 * ((1 / (2 * ε)) * (f x)^2) := by
      have hε_ne : ε ≠ 0 := ne_of_gt hε
      field_simp
    have h_ε_eq : ε * (v_test x)^2 = 2 * ((ε / 2) * (v_test x)^2) := by ring
    linarith [h_y, h_div_eq, h_ε_eq]
  have h_v_test_sq_int_Ω' : IntegrableOn (fun x : E => (v_test x)^2) Ω' volume := by
    have h_square_supp : HasCompactSupport (fun x : E => (v_test x) ^ 2) := by
      exact HasCompactSupport.intro' h_v_test_supp_cmp (isClosed_tsupport v_test)
        (fun x hx => by
          rw [image_eq_zero_of_notMem_tsupport hx]
          norm_num)
    have h_int : Integrable (fun x : E => (v_test x)^2) volume :=
      (h_v_test_cont.pow 2).integrable_of_hasCompactSupport
        h_square_supp
    exact h_int.integrableOn
  have h_f_v_int_Ω' : IntegrableOn (fun x : E => f x * v_test x) Ω' volume := by
    have h_pointwise_abs : ∀ x : E,
        |f x * v_test x| ≤ (1/2) * ((f x)^2 + (v_test x)^2) := by
      intro x
      have h_y := two_abs_mul_le_eps_sq_add (f x) (v_test x) 1 zero_lt_one
      simp only [one_mul, div_one] at h_y
      have h_abs : |f x * v_test x| = |f x| * |v_test x| := abs_mul _ _
      linarith
    have h_rhs_int : IntegrableOn (fun x : E => (1/2) * ((f x)^2 + (v_test x)^2)) Ω' volume :=
      (hf_sq_int_Ω'.add h_v_test_sq_int_Ω').const_mul (1/2)
    have h_f_AEStrong : AEStronglyMeasurable f (volume.restrict Ω') :=
      hf_memLp.aestronglyMeasurable
    have h_v_AEStrong : AEStronglyMeasurable v_test (volume.restrict Ω') :=
      h_v_test_cont.aestronglyMeasurable
    have h_prod_AEStrong : AEStronglyMeasurable (fun x : E => f x * v_test x)
        (volume.restrict Ω') := h_f_AEStrong.mul h_v_AEStrong
    refine ⟨h_prod_AEStrong, ?_⟩
    refine HasFiniteIntegral.mono' h_rhs_int.hasFiniteIntegral ?_
    refine Filter.Eventually.of_forall ?_
    intro x
    rw [Real.norm_eq_abs]
    have h_pt := h_pointwise_abs x
    have h_rhs_nn : 0 ≤ (1 : ℝ) / 2 * ((f x)^2 + (v_test x)^2) :=
      mul_nonneg (by norm_num) (add_nonneg (sq_nonneg _) (sq_nonneg _))
    exact h_pt
  have h_rhs_int_Ω' : IntegrableOn (fun x : E =>
      (ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2) Ω' volume := by
    refine (h_v_test_sq_int_Ω'.const_mul (ε/2)).add (hf_sq_int_Ω'.const_mul (1/(2*ε)))
  have h_step1 : |∫ x in Ω', f x * v_test x ∂(volume : Measure E)| ≤
      ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) :=
    abs_integral_le_integral_abs (μ := (volume : Measure E).restrict Ω')
  have h_step2 : ∫ x in Ω', |f x * v_test x| ∂(volume : Measure E) ≤
      ∫ x in Ω', ((ε/2) * (v_test x)^2 + (1/(2*ε)) * (f x)^2) ∂(volume : Measure E) := by
    refine integral_mono_ae h_f_v_int_Ω'.abs h_rhs_int_Ω' ?_
    refine Filter.Eventually.of_forall ?_
    intro x; exact h_pointwise x
  refine (h_step1.trans h_step2).trans ?_
  rw [integral_add (h_v_test_sq_int_Ω'.const_mul (ε/2)) (hf_sq_int_Ω'.const_mul (1/(2*ε)))]
  rw [integral_const_mul, integral_const_mul]
  have h_v_test_sq_Ω'_le_E :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      ∫ x, (v_test x)^2 ∂(volume : Measure E) := by
    have h_v_test_sq_eq : ∫ x, (v_test x)^2 ∂(volume : Measure E) =
        ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) := by
      have h_eq_zero : ∀ x, x ∉ Ω' → (v_test x)^2 = 0 := by
        intro x hx
        rw [h_v_test_zero_outside_Ω' x hx]; ring
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero h_eq_zero).symm
    rw [h_v_test_sq_eq]
  have h_v_test_bound := nirenbergTestFunction_sq_integral_le (d := d) hu hη hη_supp hη_range
    h_fderiv_eta k hh
  have h_v_sq_le_8N_2I :
      ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
        8 * N^2 *
          ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
        2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
          ∂(volume : Measure E) :=
    h_v_test_sq_Ω'_le_E.trans h_v_test_bound
  have h_diff_bound :
      ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_diffQuot_sq_on_tsupport_le_gradL2sqOn (d := d) hu k hh η hΩ'
      hΩ'_compact h_thick_in_Ω'
  have h_partial_le_sum : ∀ x : E,
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2 ≤
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2 := by
    intro x
    refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    exact Finset.single_le_sum (f := fun i => (diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ k)
  have h_eta_sq_partial_int : Integrable (fun x : E =>
      (η x)^2 *
        (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_partial_sq (d := d) hu hη hη_supp k k hh
  have h_eta_sq_sum_int : Integrable (fun x : E =>
      (η x)^2 *
        ∑ i : Fin d, (diffQuot k h
          (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2) volume :=
    integrable_eta_sq_diffQuot_sum (d := d) hu hη hη_supp k hh
  have h_partial_int_le :
      ∫ x, (η x)^2 *
          (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
        ∂(volume : Measure E) ≤
      ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) :=
    integral_mono h_eta_sq_partial_int h_eta_sq_sum_int h_partial_le_sum
  have h_gradL2_nn : 0 ≤ ∫ x in Ω',
        ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have h_fL2_nn : 0 ≤ ∫ x in Ω', (f x)^2 ∂(volume : Measure E) :=
    integral_nonneg (fun x => sq_nonneg _)
  have h_v_full_bound :
      (ε/2) * ∫ x in Ω', (v_test x)^2 ∂(volume : Measure E) ≤
      4 * ε * N^2 *
        ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
          ∂(volume : Measure E) +
      ε * ∫ x, (η x)^2 *
          ∑ i : Fin d, (diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
        ∂(volume : Measure E) := by
    have h_step_a := mul_le_mul_of_nonneg_left h_v_sq_le_8N_2I (by linarith : 0 ≤ ε/2)
    have h_step_b : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) +
          2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) ≤
        4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
        ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) := by
      have h1 : (ε/2) * (8 * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E)) =
          4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) := by ring
      have h2 : (ε/2) * (2 * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E)) =
          ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) := by ring
      have h_diff_pos : 0 ≤ 4 * ε * N^2 := by
        refine mul_nonneg ?_ (sq_nonneg _)
        exact mul_nonneg (by linarith) hε.le
      have h_step_c : 4 * ε * N^2 *
            ∫ x in tsupport η, (diffQuot k h u x)^2 ∂(volume : Measure E) ≤
          4 * ε * N^2 *
            ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_diff_bound h_diff_pos
      have h_step_d : ε * ∫ x, (η x)^2 *
            (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single k 1)) x)^2
            ∂(volume : Measure E) ≤
          ε * ∫ x, (η x)^2 *
            ∑ i : Fin d, (diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x)^2
            ∂(volume : Measure E) :=
        mul_le_mul_of_nonneg_left h_partial_int_le hε.le
      linarith [h1, h2]
    linarith
  have h_C_grad_le : 4 * ε * N^2 ≤ C := le_max_left _ _
  have h_C_fL2_le : 1 / (2 * ε) ≤ C := le_max_right _ _
  have h_combine :
      4 * ε * N^2 *
          ∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
            ∂(volume : Measure E) +
      (1 / (2 * ε)) * ∫ x in Ω', (f x)^2 ∂(volume : Measure E) ≤
      C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
    have h_left_le := mul_le_mul_of_nonneg_right h_C_grad_le h_gradL2_nn
    have h_right_le := mul_le_mul_of_nonneg_right h_C_fL2_le h_fL2_nn
    have h_C_dist : C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) =
        C * (∫ x in Ω', ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1))^2
              ∂(volume : Measure E)) +
        C * ∫ x in Ω', (f x)^2 ∂(volume : Measure E) := by ring
    linarith
  linarith

theorem nirenberg_master_inequality_after_young
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hη_supp : HasCompactSupport η)
    (hη_range : Set.range η ⊆ Set.Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (h_fderiv_eta : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' : Set E} (hΩ' : IsOpen Ω') (hΩ'_closure : closure Ω' ⊆ Ω)
    (hΩ'_compact : IsCompact (closure Ω'))
    {R₀ : ℝ}
    (hh_supp_in_Ω' : ∀ {h : ℝ}, |h| ≤ R₀ →
      Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u f : E → ℝ}, B.IsSmoothWeakSolution u f →
        (∀ {Ω' : Set E}, IsCompact (closure Ω') →
          MemLp f 2 (volume.restrict Ω')) →
      ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      B.lam * ∫ x, (η x)^2 *
          ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
            (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
        ∂(volume : Measure E) ≤
        (B.lam / 2) * ∫ x, (η x)^2 *
            ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
              (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
          ∂(volume : Measure E) +
        C * (∫ x in Ω',
              ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
            ∂(volume : Measure E) +
          ∫ x in Ω', (u x)^2 ∂(volume : Measure E) +
          ∫ x in Ω', (f x)^2 ∂(volume : Measure E)) := by
  classical
  set ε_eff : ℝ := B.lam / 8 with hε_eff_def
  have hε_eff_pos : 0 < ε_eff := by
    rw [hε_eff_def]; exact div_pos B.hlam_pos (by norm_num)
  obtain ⟨C1, hC1_nn, hC1⟩ := translated_coeff_cutoff_deriv_diffQuot_cross_bound (d := d) B hη
    hη_supp hη_range h_fderiv_eta hΩ' hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨C2, hC2_nn, hC2⟩ := coeff_diffQuot_cutoff_sq_gradient_cross_bound (d := d) B hη hη_supp
    hη_range
    hΩ' hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨C3, hC3_nn, hC3⟩ := coeff_diffQuot_cutoff_deriv_cross_bound (d := d) B hη hη_supp hη_range
    hN
    h_fderiv_eta hΩ' hΩ'_compact hh_supp_in_Ω' k
  obtain ⟨Cc, hCc_nn, hCc⟩ := c_term_bound (d := d) B hη hη_supp hη_range
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  obtain ⟨Cf, hCf_nn, hCf⟩ := f_term_bound (d := d) hη hη_supp hη_range
    h_fderiv_eta hΩ' hΩ'_closure hΩ'_compact hh_supp_in_Ω' k ε_eff hε_eff_pos
  set C : ℝ := max (C1 + C2 + C3 + Cc + Cf) (max Cc Cf) with hC_def
  have hC_nn : 0 ≤ C := by
    rw [hC_def]
    refine le_max_of_le_left ?_
    refine add_nonneg (add_nonneg (add_nonneg (add_nonneg hC1_nn hC2_nn) hC3_nn) hCc_nn) hCf_nn
  refine ⟨C, hC_nn, ?_⟩
  intro u f h_weak hf_l2_loc h hh hh_le
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := h_weak.1
  set I : ℝ := ∫ x, (η x)^2 *
      ∑ i : Fin d, Poincare.Analysis.Sobolev.diffQuot k h
        (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x ^ 2
    ∂(volume : Measure E) with hI_def
  set G : ℝ := ∫ x in Ω',
      ∑ i : Fin d, ((fderiv ℝ u x) (EuclideanSpace.single i 1)) ^ 2
    ∂(volume : Measure E) with hG_def
  set U : ℝ := ∫ x in Ω', (u x)^2 ∂(volume : Measure E) with hU_def
  set F : ℝ := ∫ x in Ω', (f x)^2 ∂(volume : Measure E) with hF_def
  have hI_nn : 0 ≤ I := absorbingIntegral_nonneg (d := d) k h η u
  have hG_nn : 0 ≤ G := integral_nonneg
    (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hU_nn : 0 ≤ U := integral_nonneg (fun x => sq_nonneg _)
  have hF_nn : 0 ≤ F := integral_nonneg (fun x => sq_nonneg _)
  have h_thick_in_Ω : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
    (hh_supp_in_Ω' hh_le).trans (subset_closure.trans hΩ'_closure)
  have h_master := nirenberg_master_inequality (d := d) B h_weak hη hη_supp k hh h_thick_in_Ω
  have hC1_h := hC1 hu hh hh_le
  have hC2_h := hC2 hu hh hh_le
  have hC3_h := hC3 hu hh hh_le
  have hCc_h := hCc hu hh hh_le
  have hCf_h := hCf hf_l2_loc hu hh hh_le
  have h_4ε_eq : 4 * ε_eff = B.lam / 2 := by
    rw [hε_eff_def]; ring
  have h_combine : B.lam * I ≤
      4 * ε_eff * I + (C1 + C2 + C3 + Cc + Cf) * G + Cc * U + Cf * F := by
    have h_sum_bound :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| +
          |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| +
          |∫ x in Ω, f x *
              Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| +
          |∫ x in Ω, B.c x * u x *
              Poincare.Analysis.Sobolev.NirenbergTestFunction.nirenbergTestFunction
                k h η u x| ≤
        (ε_eff * I + C1 * G) + (ε_eff * I + C2 * G) + (C3 * G) +
          (ε_eff * I + Cf * (G + F)) + (ε_eff * I + Cc * (G + U)) := by
      have h1 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := hC1_h
      have h1' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.translate k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ ε_eff * I + C1 * G := by
        rw [← abs_neg]; exact h1
      have h2 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := hC2_h
      have h2' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x,
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x)^2 *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => (fderiv ℝ u y) (EuclideanSpace.single j 1)) x
            ∂(volume : Measure E)| ≤ ε_eff * I + C2 * G := by
        rw [← abs_neg]; exact h2
      have h3 : |- ∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := hC3_h
      have h3' :
        |∑ i : Fin d, ∑ j : Fin d, ∫ x, 2 *
              Poincare.Analysis.Sobolev.diffQuot k h
                (fun y : E => B.a y i j) x * (η x) *
              ((fderiv ℝ η x) (EuclideanSpace.single j 1)) *
              ((fderiv ℝ u x) (EuclideanSpace.single i 1)) *
              Poincare.Analysis.Sobolev.diffQuot k h u x
            ∂(volume : Measure E)| ≤ C3 * G := by
        rw [← abs_neg]; exact h3
      linarith
    refine h_master.trans (h_sum_bound.trans ?_)
    have hCc_distrib : Cc * (G + U) = Cc * G + Cc * U := by ring
    have hCf_distrib : Cf * (G + F) = Cf * G + Cf * F := by ring
    linarith [hCc_distrib, hCf_distrib]
  rw [show (4 * ε_eff * I) = (B.lam / 2) * I from by rw [h_4ε_eq]] at h_combine
  have hC_grad_le : C1 + C2 + C3 + Cc + Cf ≤ C := le_max_left _ _
  have hC_Cc_le : Cc ≤ C := le_trans (le_max_left _ _) (le_max_right _ _)
  have hC_Cf_le : Cf ≤ C := le_trans (le_max_right _ _) (le_max_right _ _)
  have h_step1 : (C1 + C2 + C3 + Cc + Cf) * G ≤ C * G :=
    mul_le_mul_of_nonneg_right hC_grad_le hG_nn
  have h_step2 : Cc * U ≤ C * U :=
    mul_le_mul_of_nonneg_right hC_Cc_le hU_nn
  have h_step3 : Cf * F ≤ C * F :=
    mul_le_mul_of_nonneg_right hC_Cf_le hF_nn
  have h_C_dist : C * (G + U + F) = C * G + C * U + C * F := by ring
  linarith

end Poincare.Analysis.Sobolev.NirenbergCrossBounds
