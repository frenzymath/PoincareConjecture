import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.ProfileCalculus
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.DifferentiatedEquation

noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in

theorem exists_derivativeProfile_mul_bound {V : Set E} (hV : IsOpen V)
    (hc : IsCompact (closure V)) (r : ℕ) {a : E → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {p : ℝ≥0∞}, 1 ≤ p →
      ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
        derivativeProfile p V r (fun x => a x * u x) ≤
          ENNReal.ofReal C * derivativeProfile p V r u := by
  classical
  have hbounds : ∀ j : ℕ, ∃ A : ℝ, ∀ x ∈ closure V, ‖iteratedFDeriv ℝ j a x‖ ≤ A := by
    intro j
    exact hc.exists_bound_of_continuousOn
      (ha.continuous_iteratedFDeriv (by exact_mod_cast le_top)).continuousOn
  choose A hA using hbounds
  let B := ∑ j ∈ Finset.range (r + 1), max 0 (A j)
  have hB : 0 ≤ B := Finset.sum_nonneg fun j hj => le_max_left _ _
  have hbound : ∀ j ≤ r, ∀ x ∈ V, ‖iteratedFDeriv ℝ j a x‖ ≤ B := by
    intro j hj x hx
    exact ((hA j x (subset_closure hx)).trans (le_max_right _ _)).trans
      (Finset.single_le_sum (fun i hi => le_max_left _ _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)))
  refine ⟨cutoffMultiplier r B, cutoffMultiplier_nonneg r hB, ?_⟩
  intro p hp u hu
  exact derivativeProfile_mul_le hV hp r ha hu hB hbound

theorem differentiatedSource_profile_le {V : Set E} (hV : IsOpen V)
    (hc : IsCompact (closure V))
    (A : E → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ i j, ContDiff ℝ (⊤ : ℕ∞) (fun x => A x i j))
    (r : ℕ) (k : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u → ContDiff ℝ (⊤ : ℕ∞) f →
      derivativeProfile 2 V r
          (differentiatedSource A (fun j => Iteration.partialDeriv j u)
            (fun i j => Iteration.partialDeriv i (Iteration.partialDeriv j u))
            (Iteration.partialDeriv k f) k) ≤
        ENNReal.ofReal C *
          (derivativeProfile 2 V (r + 2) u + derivativeProfile 2 V (r + 1) f) := by
  classical
  choose C hC hboundC using fun i j =>
    exists_derivativeProfile_mul_bound hV hc r (contDiff_partial (hA i j) k)
  choose D hD hboundD using fun i j =>
    exists_derivativeProfile_mul_bound hV hc r
      (contDiff_partial (contDiff_partial (hA i j) k) i)
  let S : ℝ := ∑ i, ∑ j, (C i j + D i j)
  have hS : 0 ≤ S := Finset.sum_nonneg fun i hi =>
    Finset.sum_nonneg fun j hj => add_nonneg (hC i j) (hD i j)
  refine ⟨1 + S, by positivity, ?_⟩
  intro u f hu hf
  let U := derivativeProfile 2 V (r + 2) u
  let F := derivativeProfile 2 V (r + 1) f
  let term : Fin d → Fin d → E → ℝ := fun i j x =>
    Iteration.partialDeriv k (fun y => A y i j) x *
        Iteration.partialDeriv i (Iteration.partialDeriv j u) x +
      Iteration.partialDeriv i (Iteration.partialDeriv k (fun y => A y i j)) x *
        Iteration.partialDeriv j u x
  have hterm (i j) : ContDiff ℝ (⊤ : ℕ∞) (term i j) :=
    ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i)).add
      ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))
  have htermBound (i j) : derivativeProfile 2 V r (term i j) ≤
      ENNReal.ofReal (C i j + D i j) * U := by
    have hfirst := hboundC i j (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (contDiff_partial (contDiff_partial hu j) i)
    have hsecond := hboundD i j (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (contDiff_partial hu j)
    have hdu : derivativeProfile 2 V r (Iteration.partialDeriv j u) ≤ U :=
      (derivativeProfile_partial_le r j hu).trans
        (derivativeProfile_mono_order (Nat.le_succ (r + 1)) u)
    have hddu : derivativeProfile 2 V r
        (Iteration.partialDeriv i (Iteration.partialDeriv j u)) ≤ U :=
      (derivativeProfile_partial_le r i (contDiff_partial hu j)).trans
        (derivativeProfile_partial_le (r + 1) j hu)
    calc
      derivativeProfile 2 V r (term i j) ≤
          derivativeProfile 2 V r (fun x => Iteration.partialDeriv k (fun y => A y i j) x *
            Iteration.partialDeriv i (Iteration.partialDeriv j u) x) +
          derivativeProfile 2 V r (fun x =>
            Iteration.partialDeriv i (Iteration.partialDeriv k (fun y => A y i j)) x *
              Iteration.partialDeriv j u x) :=
        derivativeProfile_add_le hV (by norm_num) r
          ((contDiff_partial (hA i j) k).mul (contDiff_partial (contDiff_partial hu j) i))
          ((contDiff_partial (contDiff_partial (hA i j) k) i).mul (contDiff_partial hu j))
      _ ≤ ENNReal.ofReal (C i j) * U + ENNReal.ofReal (D i j) * U := by
        gcongr
        · exact hfirst.trans (by gcongr)
        · exact hsecond.trans (by gcongr)
      _ = ENNReal.ofReal (C i j + D i j) * U := by
        rw [ENNReal.ofReal_add (hC i j) (hD i j), add_mul]
  have hsum : derivativeProfile 2 V r (fun x => ∑ i, ∑ j, term i j x) ≤
      ENNReal.ofReal S * U := by
    apply (derivativeProfile_finset_sum_le hV (by norm_num) r Finset.univ
      (fun i hi => ContDiff.sum (fun j hj => hterm i j))).trans
    change (∑ i, derivativeProfile 2 V r (fun x => ∑ j, term i j x)) ≤
      ENNReal.ofReal (∑ i, ∑ j, (C i j + D i j)) * U
    rw [ENNReal.ofReal_sum_of_nonneg
      (fun i hi => Finset.sum_nonneg fun j hj => add_nonneg (hC i j) (hD i j)),
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    apply (derivativeProfile_finset_sum_le hV (by norm_num) r Finset.univ
      (fun j hj => hterm i j)).trans
    rw [ENNReal.ofReal_sum_of_nonneg (fun j hj => add_nonneg (hC i j) (hD i j)),
      Finset.sum_mul]
    exact Finset.sum_le_sum fun j hj => htermBound i j
  have hsmoothSum : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i, ∑ j, term i j x) :=
    ContDiff.sum (fun i hi => ContDiff.sum (fun j hj => hterm i j))
  have hsource := derivativeProfile_add_le hV (by norm_num : (1 : ℝ≥0∞) ≤ 2) r
    (contDiff_partial hf k)
    hsmoothSum
  change derivativeProfile 2 V r (fun x => Iteration.partialDeriv k f x +
    ∑ i, ∑ j, term i j x) ≤ _
  apply hsource.trans
  apply (add_le_add (derivativeProfile_partial_le r k hf) hsum).trans
  rw [ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1) hS, ENNReal.ofReal_one]
  calc
    F + ENNReal.ofReal S * U ≤ (1 + ENNReal.ofReal S) * F +
        (1 + ENNReal.ofReal S) * U := by
      apply add_le_add
      · calc
          F = 1 * F := (one_mul F).symm
          _ ≤ (1 + ENNReal.ofReal S) * F := by gcongr; exact le_self_add
      · gcongr; exact le_add_self
    _ = (1 + ENNReal.ofReal S) * (U + F) := by ring

end Poincare.Analysis.Elliptic.InteriorEstimates
