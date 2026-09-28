import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.Substitution.Assembly

noncomputable section

open MeasureTheory Metric Filter Topology Set Function
open scoped ENNReal NNReal BigOperators

namespace Poincare.Analysis.Elliptic.InteriorEstimates

open Poincare.Analysis.Sobolev
open NirenbergEuclidean NirenbergCrossBoundsNonSmooth NirenbergStandardTest
open NirenbergSubstitutionNonSmooth NirenbergAssembly

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem energy_le_of_flux_identity {L P C1 C2 C3 R Q : ℝ}
    (hcoer : L ≤ P) (hid : -(P + C1 + C2 + C3) = R) :
    L ≤ |C1| + |C2| + |C3| + |R| + |Q| := by
  linarith [neg_le_abs C1, neg_le_abs C2, neg_le_abs C3, neg_le_abs R, abs_nonneg Q]

theorem diffQuot_weakGradient_localL2_bound_quantitative
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
    ∀ ⦃h : ℝ⦄, h ≠ 0 → |h| ≤ R₀ →
      (B.lam / 2) * (∫ x in Ω'', ∑ i : Fin d, (diffQuot k h (p i) x) ^ 2) ≤
        nirenbergMasterYoungConstant B N hΩ'c k *
          ((∫ x in Ω', ∑ i : Fin d, (p i x) ^ 2) +
            (∫ x in Ω', (u x) ^ 2) + (∫ x in Ω', (f x) ^ 2)) := by
  classical
  refine nirenberg_diffQuot_g_localL2_bound_quantitative B hu
    (fun {_} _ => hf.restrict _) hp hη hηc hηrange hN hDη hΩ' hΩ'Ω
    hΩ'c hthick hηone hΩ'' k ?_ ?_ ?_
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

end Poincare.Analysis.Elliptic.InteriorEstimates
