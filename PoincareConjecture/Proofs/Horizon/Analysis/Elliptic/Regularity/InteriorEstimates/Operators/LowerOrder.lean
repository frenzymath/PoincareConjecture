import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Commutator
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic




noncomputable section

open Set MeasureTheory
open scoped ENNReal ContDiff
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Sobolev.NirenbergEuclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

def driftCorrection (a : E → Matrix (Fin d) (Fin d) ℝ)
    (b : Fin d → E → ℝ) (j : Fin d) : E → ℝ := fun x =>
  b j x - ∑ i, partialDeriv i (fun y => a y i j) x

theorem contDiff_driftCorrection
    {a : E → Matrix (Fin d) (Fin d) ℝ} {b : Fin d → E → ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (j : Fin d) :
    ContDiff ℝ ∞ (driftCorrection a b j) :=
  (hb j).sub (ContDiff.sum (fun i _ => contDiff_partial (ha i j) i))

theorem contDiff_principalSource
    {a : E → Matrix (Fin d) (Fin d) ℝ}
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    {u : E → ℝ} (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (principalSource a u) :=
  (ContDiff.sum (fun i _ => contDiff_partial
    (ContDiff.sum (fun j _ => (ha i j).mul (contDiff_partial hu j))) i)).neg

theorem derivativeProfile_neg (p : ℝ≥0∞) (V : Set E) (r : ℕ) (u : E → ℝ) :
    derivativeProfile p V r (fun x => -u x) = derivativeProfile p V r u := by
  change derivativeProfile p V r (-u) = _
  simp only [derivativeProfile, iteratedFDeriv_neg_apply, norm_neg]

theorem exists_principalSource_profile_le [NeZero d]
    {V : Set E} (hV : IsOpen V) (hVc : IsCompact (closure V))
    (a : E → Matrix (Fin d) (Fin d) ℝ) (b : Fin d → E → ℝ)
    (ha : ∀ i j, ContDiff ℝ ∞ (fun x => a x i j))
    (hb : ∀ i, ContDiff ℝ ∞ (b i)) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ ∞ u →
      derivativeProfile 2 V r (principalSource a u) ≤ ENNReal.ofReal C *
        (derivativeProfile 2 V r (secondOrderOperator a b u) +
          derivativeProfile 2 V (r + 1) u) := by
  choose A hA hbound using fun i => exists_derivativeProfile_mul_bound
    hV hVc r (contDiff_driftCorrection ha hb i)
  let S : ℝ := ∑ i, A i
  have hS : 0 ≤ S := Finset.sum_nonneg (fun i _ => hA i)
  refine ⟨1 + S, by positivity, ?_⟩
  intro u hu
  have hL := contDiff_secondOrderOperator ha hb hu
  have hsum : ContDiff ℝ ∞ (fun x => ∑ i, driftCorrection a b i x * partialDeriv i u x) :=
    ContDiff.sum (fun i _ => (contDiff_driftCorrection ha hb i).mul (contDiff_partial hu i))
  have hid : principalSource a u = fun x => -secondOrderOperator a b u x +
      ∑ i, driftCorrection a b i x * partialDeriv i u x := by
    funext x
    exact principalSource_eq_secondOrderOperator b ha hu x
  have hsumBound : derivativeProfile 2 V r
      (fun x => ∑ i, driftCorrection a b i x * partialDeriv i u x) ≤
      ENNReal.ofReal S * derivativeProfile 2 V (r + 1) u := by
    apply (derivativeProfile_finset_sum_le hV (by norm_num) r Finset.univ
      (fun i _ => (contDiff_driftCorrection ha hb i).mul (contDiff_partial hu i))).trans
    rw [show ENNReal.ofReal S = ∑ i, ENNReal.ofReal (A i) from
      ENNReal.ofReal_sum_of_nonneg (fun i _ => hA i), Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply (hbound i (by norm_num : (1 : ℝ≥0∞) ≤ 2) (contDiff_partial hu i)).trans
    gcongr
    exact derivativeProfile_partial_le r i hu
  rw [hid]
  apply (derivativeProfile_add_le hV (by norm_num) r hL.neg hsum).trans
  rw [derivativeProfile_neg]
  apply (add_le_add le_rfl hsumBound).trans
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hS, ENNReal.ofReal_one, mul_add]
  apply add_le_add
  · exact le_mul_of_one_le_left' (by exact le_self_add)
  · gcongr
    exact le_add_self

end Poincare.Analysis.Elliptic.InteriorEstimates
