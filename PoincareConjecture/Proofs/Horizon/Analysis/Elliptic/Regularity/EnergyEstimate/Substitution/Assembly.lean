import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.Weak
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.WeakEquation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.NirenbergBound
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.DifferenceQuotient.WeakDerivative








noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal BigOperators

namespace Poincare.Analysis.Sobolev.NirenbergAssembly

open NirenbergEuclidean NirenbergCrossBoundsNonSmooth NirenbergStandardTest
open NirenbergSubstitutionNonSmooth

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
private theorem integrable_cutoff_mul_mul
    {a v w : E → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hv : MemLp v 2 volume) (hw : MemLp w 2 volume) :
    Integrable (fun x => a x * v x * w x) volume := by
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous_compactSupport ha hac
  have ham := memLp_bounded_mul ha.aestronglyMeasurable hC hv
  simpa only [Pi.mul_def] using ham.integrable_mul hw

omit [NeZero d] in
private theorem diffQuot_flux
    (A : E → Fin d → Fin d → ℝ) (p : Fin d → E → ℝ)
    (k j : Fin d) {h : ℝ} (hh : h ≠ 0) (x : E) :
    diffQuot k h (fun y => ∑ i, A y i j * p i y) x =
      ∑ i, (translate k h (fun y => A y i j) x * diffQuot k h (p i) x +
        diffQuot k h (fun y => A y i j) x * p i x) := by
  simp only [diffQuot_apply_of_ne k hh]
  rw [← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [translate]
  ring


theorem flux_pairing_expansion
    {Ω : Set E} (B : SmoothEllipticBilinearForm d Ω)
    {u : E → ℝ} (hu : MemLp u 2 volume)
    {p : Fin d → E → ℝ} (hp : ∀ i, MemLp (p i) 2 volume)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0) :
    (∑ j : Fin d, ∫ x,
      diffQuot k h (fun y => ∑ i : Fin d, B.a y i j * p i y) x *
        (η x ^ 2 * diffQuot k h (p j) x +
          2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) * diffQuot k h u x)) =
    (∫ x, ∑ i : Fin d, ∑ j : Fin d,
      translate k h (fun y => B.a y i j) x * η x ^ 2 *
        diffQuot k h (p i) x * diffQuot k h (p j) x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * translate k h (fun y => B.a y i j) x * η x *
        (fderiv ℝ η x) (EuclideanSpace.single j 1) *
        diffQuot k h (p i) x * diffQuot k h u x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x,
      diffQuot k h (fun y => B.a y i j) x * η x ^ 2 * p i x *
        diffQuot k h (p j) x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x,
      2 * diffQuot k h (fun y => B.a y i j) x * η x *
        (fderiv ℝ η x) (EuclideanSpace.single j 1) * p i x * diffQuot k h u x) := by
  classical
  let P := fun (i j : Fin d) (x : E) =>
    translate k h (fun y => B.a y i j) x * η x ^ 2 *
      diffQuot k h (p i) x * diffQuot k h (p j) x
  let C1 := fun (i j : Fin d) (x : E) =>
    2 * translate k h (fun y => B.a y i j) x * η x *
      (fderiv ℝ η x) (EuclideanSpace.single j 1) *
      diffQuot k h (p i) x * diffQuot k h u x
  let C2 := fun (i j : Fin d) (x : E) =>
    diffQuot k h (fun y => B.a y i j) x * η x ^ 2 * p i x * diffQuot k h (p j) x
  let C3 := fun (i j : Fin d) (x : E) =>
    2 * diffQuot k h (fun y => B.a y i j) x * η x *
      (fderiv ℝ η x) (EuclideanSpace.single j 1) * p i x * diffQuot k h u x
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    simp only [pow_two]
    exact hηc.mul_right
  have hDη (j : Fin d) : Continuous
      (fun x => (fderiv ℝ η x) (EuclideanSpace.single j 1)) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hτ (i j : Fin d) : Continuous (translate k h (fun y => B.a y i j)) :=
    continuous_translate k h (B.continuous_a i j)
  have hδ (i j : Fin d) : Continuous (diffQuot k h (fun y => B.a y i j)) :=
    continuous_diffQuot_of_continuous k h (B.continuous_a i j)
  have hdp (i : Fin d) := memLp_diffQuot_two k h (hp i)
  have hdu := memLp_diffQuot_two k h hu
  have hP (i j : Fin d) : Integrable (P i j) volume :=
    integrable_cutoff_mul_mul ((hτ i j).mul (hη.continuous.pow 2))
      hη2c.mul_left (hdp i) (hdp j)
  have hC1 (i j : Fin d) : Integrable (C1 i j) volume :=
    integrable_cutoff_mul_mul
      (((continuous_const.mul (hτ i j)).mul hη.continuous).mul (hDη j))
      (hηc.mul_left.mul_right) (hdp i) hdu
  have hC2 (i j : Fin d) : Integrable (C2 i j) volume :=
    integrable_cutoff_mul_mul ((hδ i j).mul (hη.continuous.pow 2))
      hη2c.mul_left (hp i) (hdp j)
  have hC3 (i j : Fin d) : Integrable (C3 i j) volume :=
    integrable_cutoff_mul_mul
      (((continuous_const.mul (hδ i j)).mul hη.continuous).mul (hDη j))
      (hηc.mul_left.mul_right) (hp i) hdu
  have hrow (j : Fin d) :
      (fun x => diffQuot k h (fun y => ∑ i : Fin d, B.a y i j * p i y) x *
        (η x ^ 2 * diffQuot k h (p j) x +
          2 * η x * (fderiv ℝ η x) (EuclideanSpace.single j 1) * diffQuot k h u x)) =
      fun x => ∑ i : Fin d, (P i j x + C1 i j x + C2 i j x + C3 i j x) := by
    funext x
    rw [diffQuot_flux B.a p k j hh x, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [P, C1, C2, C3]
    ring
  simp_rw [hrow]
  have hsumP : (∫ x, ∑ i : Fin d, ∑ j : Fin d, P i j x) =
      ∑ i : Fin d, ∑ j : Fin d, ∫ x, P i j x := by
    rw [integral_finsetSum _ (fun i _ =>
      integrable_finsetSum _ (fun j _ => hP i j))]
    apply Finset.sum_congr rfl
    intro i _
    exact integral_finsetSum _ (fun j _ => hP i j)
  change (∑ j : Fin d, ∫ x, ∑ i : Fin d, (P i j x + C1 i j x + C2 i j x + C3 i j x)) =
    (∫ x, ∑ i : Fin d, ∑ j : Fin d, P i j x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x, C1 i j x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x, C2 i j x) +
    (∑ i : Fin d, ∑ j : Fin d, ∫ x, C3 i j x)
  rw [hsumP]
  have hsplit (j : Fin d) :
      (∫ x, ∑ i : Fin d, (P i j x + C1 i j x + C2 i j x + C3 i j x)) =
      ∑ i : Fin d, ((∫ x, P i j x) + (∫ x, C1 i j x) +
        (∫ x, C2 i j x) + (∫ x, C3 i j x)) := by
    have hint (i : Fin d) :
        Integrable (fun x => P i j x + C1 i j x + C2 i j x + C3 i j x) volume := by
      simpa only [Pi.add_def] using
        (((hP i j).add (hC1 i j)).add (hC2 i j)).add (hC3 i j)
    rw [integral_finsetSum _ (fun i _ => hint i)]
    apply Finset.sum_congr rfl
    intro i _
    have h01 : Integrable (fun x => P i j x + C1 i j x) volume :=
      (hP i j).add (hC1 i j)
    have h012 : Integrable (fun x => P i j x + C1 i j x + C2 i j x) volume :=
      h01.add (hC2 i j)
    rw [integral_add h012 (hC3 i j), integral_add h01 (hC2 i j),
      integral_add (hP i j) (hC1 i j)]
  simp_rw [hsplit]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_add_distrib]

private theorem energy_le_of_flux_identity {L P C1 C2 C3 R Q : ℝ}
    (hcoer : L ≤ P) (hid : -(P + C1 + C2 + C3) = R) :
    L ≤ |C1| + |C2| + |C3| + |R| + |Q| := by
  linarith [neg_le_abs C1, neg_le_abs C2, neg_le_abs C3, neg_le_abs R, abs_nonneg Q]








theorem diffQuot_weakGradient_localL2_bound
    {Ω V : Set E} (B : SmoothEllipticBilinearForm d Ω) (hV : IsOpen V)
    {u f : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    (hp : ∀ i, MemLp (p i) 2 volume)
    (hw : ∀ i, Weak.HasWeakPartialDeriv i (p i) u univ)
    (hF : ∀ j, MemLp (fun x => ∑ i : Fin d, B.a x i j * p i x) 2 volume)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ V →
      (∫ x in V, ∑ j : Fin d,
        (∑ i : Fin d, B.a x i j * p i x) *
          fderiv ℝ φ x (EuclideanSpace.single j 1)) = ∫ x in V, f x * φ x)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    {N : ℝ} (hN : 0 ≤ N) (hDη : ∀ x : E, ‖fderiv ℝ η x‖ ≤ N)
    {Ω' Ω'' : Set E} (hΩ' : IsOpen Ω') (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ'c : IsCompact (closure Ω')) (hΩ'V : Ω' ⊆ V)
    {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hthick : ∀ {h : ℝ}, |h| ≤ R₀ → Metric.cthickening |h| (tsupport η) ⊆ Ω')
    (hηone : ∀ x ∈ Ω'', η x = 1) (hΩ'' : MeasurableSet Ω'') (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {h : ℝ}, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * (∫ x in Ω'', ∑ i : Fin d, (diffQuot k h (p i) x) ^ 2) ≤
        C * ((∫ x in Ω', ∑ i : Fin d, (p i x) ^ 2) +
          (∫ x in Ω', (u x) ^ 2) + (∫ x in Ω', (f x) ^ 2)) := by
  classical
  refine nirenberg_diffQuot_g_localL2_bound B hu (fun {_} _ => hf.restrict _) hp
    hη hηc hηrange hN hDη hΩ' hΩ'Ω hΩ'c hthick hηone hΩ'' k ?_ ?_ ?_
  · intro h hh hh_le
    have hthick' : Metric.cthickening R₀ (closure (tsupport η)) ⊆ Ω' := by
      simpa only [(isClosed_tsupport η).closure_eq, abs_of_pos hR₀] using
        hthick (h := R₀) (by rw [abs_of_pos hR₀])
    have hFK := integral_sq_diffQuot_le_integral_sq_weakPartial_meas hu (hp k) k
      (hw k) hΩ'.measurableSet (isClosed_tsupport η).measurableSet
      (by simpa only [(isClosed_tsupport η).closure_eq] using hηc.isCompact)
      hR₀ hthick' hh hh_le
    refine hFK.trans (integral_mono ?_ ?_ ?_)
    · exact ((hp k).integrable_sq).restrict
    · exact integrable_finsetSum _ (fun i _ => (hp i).integrable_sq.restrict)
    · intro x
      exact Finset.single_le_sum (fun i _ => sq_nonneg (p i x)) (Finset.mem_univ k)
  · intro h hh _
    exact nirenbergTestFunction_sq_integral_le_weak hu (hp k) k (hw k)
      hη hηc hηrange hDη hh
  · intro h hh hh_le
    have hcoer := principal_term_ge_lambda_norm_sq_nonsmooth B hp hη hηc
      hΩ'Ω hthick k hh_le
    have htestΩ' : tsupport (standardNirenbergTest k h η u) ⊆ Ω' :=
      (NirenbergTestFunction.tsupport_nirenbergTestFunction_subset η u k h).trans
        (hthick hh_le)
    have hzero (x : E) (hx : x ∉ Ω') : f x * standardNirenbergTest k h η u x = 0 := by
      rw [image_eq_zero_of_notMem_tsupport (fun hmem => hx (htestΩ' hmem)), mul_zero]
    have hR : (∫ x in V, f x * standardNirenbergTest k h η u x) =
        ∫ x in Ω, f x * NirenbergTestFunction.nirenbergTestFunction k h η u x := by
      rw [setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzero x (fun hmem => hx (hΩ'V hmem)))]
      exact (setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => hzero x (fun hmem => hx (hΩ'Ω (subset_closure hmem))))).symm
    have hid := Poincare.Analysis.Elliptic.nirenberg_weakEquation_identity hV
      hF (hf.restrict V) hu hp hw heq hη hηc k hh ((hthick hh_le).trans hΩ'V)
    simp only [Poincare.Analysis.Elliptic.nirenbergTestPartial] at hid
    rw [flux_pairing_expansion B hu hp hη hηc k hh, hR] at hid
    exact energy_le_of_flux_identity hcoer hid

end Poincare.Analysis.Sobolev.NirenbergAssembly
