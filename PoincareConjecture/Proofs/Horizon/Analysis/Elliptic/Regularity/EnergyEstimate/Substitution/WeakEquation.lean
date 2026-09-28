import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.WeakTestExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Standard
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.CrossTerms.Principal

noncomputable section

open Set MeasureTheory Filter
open scoped Topology ENNReal
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth
open Poincare.Analysis.Sobolev.NirenbergStandardTest

namespace Poincare.Analysis.Elliptic

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem memLp_continuous_compactSupport_mul
    {a v : E → ℝ} (ha : Continuous a) (hac : HasCompactSupport a)
    (hv : MemLp v 2 volume) : MemLp (fun x => a x * v x) 2 volume := by
  obtain ⟨C, _, hC⟩ := exists_bound_of_continuous_compactSupport ha hac
  exact memLp_bounded_mul ha.aestronglyMeasurable hC hv

omit [NeZero d] in
theorem diffQuot_eq_zero_of_notMem_cthickening
    {K : Set E} {v : E → ℝ} (hv : ∀ x ∉ K, v x = 0)
    (k : Fin d) (h : ℝ) {x : E} (hx : x ∉ Metric.cthickening |h| K) :
    diffQuot k h v x = 0 := by
  have hxK : x ∉ K := fun hmem => hx (Metric.self_subset_cthickening K hmem)
  have hxshift : x + h • EuclideanSpace.single k 1 ∉ K := by
    intro hmem
    apply hx
    apply Metric.mem_cthickening_of_dist_le _ (x + h • EuclideanSpace.single k 1) _ K hmem
    simp [dist_eq_norm, norm_smul, Real.norm_eq_abs]
  by_cases hh : h = 0
  · simp [hh]
  · rw [diffQuot_apply_of_ne k hh, hv x hxK, hv _ hxshift]
    simp

def nirenbergTestPartial (k i : Fin d) (h : ℝ) (η u : E → ℝ)
    (p : Fin d → E → ℝ) : E → ℝ := fun x =>
  η x ^ 2 * diffQuot k h (p i) x +
    2 * η x * fderiv ℝ η x (EuclideanSpace.single i 1) * diffQuot k h u x

omit [NeZero d] in
theorem nirenbergTestPartial_memLp
    {u : E → ℝ} {p : Fin d → E → ℝ}
    (hu : MemLp u 2 volume) (hp : ∀ i, MemLp (p i) 2 volume)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k i : Fin d) (h : ℝ) : MemLp (nirenbergTestPartial k i h η u p) 2 volume := by
  have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
    simp only [pow_two]
    exact hηc.mul_right
  have hterm : Continuous (fun x => 2 * η x *
      fderiv ℝ η x (EuclideanSpace.single i 1)) :=
    (continuous_const.mul hη.continuous).mul
      ((hη.continuous_fderiv (by simp)).clm_apply continuous_const)
  have htermc : HasCompactSupport (fun x => 2 * η x *
      fderiv ℝ η x (EuclideanSpace.single i 1)) :=
    (hηc.mul_left : HasCompactSupport (fun x => 2 * η x)).mul_right
  exact (memLp_continuous_compactSupport_mul (hη.continuous.pow 2) hη2c
    (memLp_diffQuot_two k h (hp i))).add
      (memLp_continuous_compactSupport_mul hterm htermc (memLp_diffQuot_two k h hu))

omit [NeZero d] in
theorem nirenbergTestPartial_zero {η u : E → ℝ} {p : Fin d → E → ℝ}
    (k i : Fin d) (h : ℝ) {x : E} (hx : x ∉ tsupport η) :
    nirenbergTestPartial k i h η u p x = 0 := by
  simp [nirenbergTestPartial, image_eq_zero_of_notMem_tsupport hx]

theorem nirenberg_weakEquation_identity
    {O : Set E} (hO : IsOpen O) {F p : Fin d → E → ℝ} {f u : E → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hf : MemLp f 2 (volume.restrict O))
    (hu : MemLp u 2 volume) (hp : ∀ i, MemLp (p i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (p i) u univ)
    (heq : ∀ φ : E → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x in O, ∑ i, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x in O, f x * φ x)
    {η : E → ℝ} (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (k : Fin d) {h : ℝ} (hh : h ≠ 0)
    (hsupp : Metric.cthickening |h| (tsupport η) ⊆ O) :
    -(∑ i, ∫ x, diffQuot k h (F i) x * nirenbergTestPartial k i h η u p x) =
      ∫ x in O, f x * standardNirenbergTest k h η u x := by
  let v := standardNirenbergTest k h η u
  let q : Fin d → E → ℝ := fun i => diffQuot k (-h) (nirenbergTestPartial k i h η u p)
  have hr (i : Fin d) := nirenbergTestPartial_memLp hu hp hη hηc k i h
  have hq (i : Fin d) : MemLp (q i) 2 volume := memLp_diffQuot_two k (-h) (hr i)
  have hv : MemLp v 2 volume := by
    have hη2c : HasCompactSupport (fun x => η x ^ 2) := by
      simp only [pow_two]
      exact hηc.mul_right
    exact memLp_diffQuot_two k (-h)
      (memLp_continuous_compactSupport_mul (hη.continuous.pow 2) hη2c
        (memLp_diffQuot_two k h hu))
  have hwq (i : Fin d) : HasWeakPartialDeriv i (q i) v O := by
    apply HasWeakPartialDeriv.restrict hO (subset_univ O)
    exact hasWeakPartialDeriv_standardNirenbergTest k i h hη
      (by simpa using hu.locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2))
      (by simpa using (hp i).locallyIntegrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)) (hw i)
  have hvc := standardNirenbergTest_hasCompactSupport k h hηc u
  have hvO : tsupport v ⊆ O :=
    (NirenbergTestFunction.tsupport_nirenbergTestFunction_subset η u k h).trans hsupp
  have hvEq := weakEquation_of_compact_memW1p hO (fun i => (hF i).restrict O) hf
    heq (hv.restrict O) (fun i => (hq i).restrict O) hwq hvc hvO
  have hqzero (i : Fin d) (x : E) (hx : x ∉ O) : q i x = 0 := by
    apply diffQuot_eq_zero_of_notMem_cthickening
      (fun y hy => nirenbergTestPartial_zero k i h hy) k (-h)
    simpa only [abs_neg] using (fun hmem => hx (hsupp hmem))
  have hsumzero (x : E) (hx : x ∉ O) : (∑ i, F i x * q i x) = 0 := by
    simp [hqzero _ x hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsumzero] at hvEq
  have hsum : (∫ x, ∑ i, F i x * q i x) = ∑ i, ∫ x, F i x * q i x := by
    simpa using integral_finsetSum Finset.univ (fun i _ => (hF i).integrable_mul (hq i))
  rw [hsum] at hvEq
  have hibp (i : Fin d) : (∫ x, F i x * q i x) =
      -(∫ x, diffQuot k h (F i) x * nirenbergTestPartial k i h η u p x) := by
    have hi := integral_diffQuot_mul_eq_neg_integral_mul_diffQuot k hh (hF i) (hr i)
    dsimp [q]
    linarith
  simpa only [hibp, Finset.sum_neg_distrib] using hvEq

end Poincare.Analysis.Elliptic
