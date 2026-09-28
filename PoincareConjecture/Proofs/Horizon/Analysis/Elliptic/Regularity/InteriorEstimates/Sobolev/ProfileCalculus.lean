import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Profile
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Iteration.TestCalculus

noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem derivativeProfile_mono_order {Ω : Set E} {p : ℝ≥0∞} {r s : ℕ}
    (hrs : r ≤ s) (u : E → ℝ) :
    derivativeProfile p Ω r u ≤ derivativeProfile p Ω s u := by
  unfold derivativeProfile
  exact Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.range_subset_range.mpr (Nat.add_le_add_right hrs 1))
    (fun i hi hn => zero_le)

theorem derivativeProfile_mono_set {V W : Set E} (hWV : W ⊆ V)
    (p : ℝ≥0∞) (r : ℕ) (u : E → ℝ) :
    derivativeProfile p W r u ≤ derivativeProfile p V r u := by
  unfold derivativeProfile
  exact Finset.sum_le_sum fun j hj =>
    eLpNorm_mono_measure _ (Measure.restrict_mono hWV le_rfl)

theorem derivativeProfile_add_le [NeZero d] {Ω : Set E} (_hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {u v : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hv : ContDiff ℝ (⊤ : ℕ∞) v) :
    derivativeProfile p Ω r (fun x => u x + v x) ≤
      derivativeProfile p Ω r u + derivativeProfile p Ω r v := by
  classical
  unfold derivativeProfile
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j hj
  have huj : ContDiff ℝ j u := hu.of_le (by exact_mod_cast le_top)
  have hvj : ContDiff ℝ j v := hv.of_le (by exact_mod_cast le_top)
  have hsum : (fun x => ‖iteratedFDeriv ℝ j (fun y => u y + v y) x‖) =
      (fun x => ‖iteratedFDeriv ℝ j u x + iteratedFDeriv ℝ j v x‖) := by
    funext x
    exact congrArg norm (fun_iteratedFDeriv_add_apply huj.contDiffAt hvj.contDiffAt)
  rw [hsum, eLpNorm_norm, eLpNorm_norm, eLpNorm_norm]
  exact eLpNorm_add_le
    (hu.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable
    (hv.continuous_iteratedFDeriv (by exact_mod_cast le_top)).aestronglyMeasurable hp

theorem derivativeProfile_finset_sum_le [NeZero d] {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {ι : Type*} (s : Finset ι)
    {u : ι → E → ℝ} (hu : ∀ i ∈ s, ContDiff ℝ (⊤ : ℕ∞) (u i)) :
    derivativeProfile p Ω r (fun x => ∑ i ∈ s, u i x) ≤
      ∑ i ∈ s, derivativeProfile p Ω r (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [derivativeProfile]
  | @insert i s hi ih =>
      have hsum := derivativeProfile_add_le hΩ hp r
        (hu i (Finset.mem_insert_self i s))
        (by
          simpa only [Finset.sum_insert hi] using
            ContDiff.sum (fun j hj => hu j (Finset.mem_insert_of_mem hj)))
      simpa only [Finset.sum_insert hi] using hsum.trans (add_le_add le_rfl
        (ih (fun j hj => hu j (Finset.mem_insert_of_mem hj))))

theorem derivativeProfile_partial_le [NeZero d] {Ω : Set E}
    {p : ℝ≥0∞} (r : ℕ) (i : Fin d) {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    derivativeProfile p Ω r (Iteration.partialDeriv i u) ≤
      derivativeProfile p Ω (r + 1) u := by
  classical
  unfold derivativeProfile
  calc
    ∑ j ∈ Finset.range (r + 1),
        eLpNorm (fun x => ‖iteratedFDeriv ℝ j (Iteration.partialDeriv i u) x‖) p
          (volume.restrict Ω) ≤
        ∑ j ∈ Finset.range (r + 1),
          eLpNorm (fun x => ‖iteratedFDeriv ℝ (j + 1) u x‖) p
            (volume.restrict Ω) := by
      apply Finset.sum_le_sum
      intro j hj
      apply eLpNorm_mono_ae
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_norm, norm_norm]
        change ‖iteratedFDeriv ℝ j (fun y => (fderiv ℝ u y) (EuclideanSpace.single i 1)) x‖ ≤ _
        exact norm_iteratedFDeriv_partial_le hu i j x
    _ ≤ ∑ j ∈ Finset.range (r + 1 + 1),
        eLpNorm (fun x => ‖iteratedFDeriv ℝ j u x‖) p (volume.restrict Ω) := by
      rw [Finset.sum_range_succ' (n := r + 1)]
      exact le_self_add

theorem norm_iteratedFDeriv_succ_le_sum_partial {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (r : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (r + 1) u x‖ ≤
      ∑ i : Fin d, ‖iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x‖ := by
  classical
  have hfd : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ u) :=
    hu.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  rw [← norm_iteratedFDeriv_fderiv]
  apply ContinuousMultilinearMap.opNorm_le_bound
    (Finset.sum_nonneg (fun i hi => norm_nonneg _))
  intro v
  apply ContinuousLinearMap.opNorm_le_bound (iteratedFDeriv ℝ r (fderiv ℝ u) x v)
    (mul_nonneg (Finset.sum_nonneg (fun i hi => norm_nonneg _))
      (Finset.prod_nonneg (fun i hi => norm_nonneg _)))
  intro w
  have h_expand : w = ∑ i : Fin d, w i • EuclideanSpace.single i (1 : ℝ) := by
    have h := (EuclideanSpace.basisFun (Fin d) ℝ).sum_repr w
    rw [show (fun i : Fin d => w i • EuclideanSpace.single i (1 : ℝ)) =
      (fun i : Fin d => (EuclideanSpace.basisFun (Fin d) ℝ).repr w i •
        (EuclideanSpace.basisFun (Fin d) ℝ) i) from ?_, h]
    funext i
    rw [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply]
  have happly (i : Fin d) :
      iteratedFDeriv ℝ r (fderiv ℝ u) x v (EuclideanSpace.single i 1) =
        iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x v := by
    exact (iteratedFDeriv_clm_apply_const_apply hfd
      (by exact_mod_cast le_top)).symm
  calc
    ‖(iteratedFDeriv ℝ r (fderiv ℝ u) x v) w‖ =
        ‖∑ i : Fin d, w i • iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x v‖ := by
      conv_lhs => rw [h_expand]
      rw [map_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      rw [map_smul, happly]
    _ ≤ ∑ i : Fin d, ‖w i • iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x v‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin d, ‖w‖ *
        (‖iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x‖ * ∏ a, ‖v a‖) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      exact mul_le_mul (PiLp.norm_apply_le w i)
        ((iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x).le_opNorm v)
        (norm_nonneg _) (norm_nonneg _)
    _ = (∑ i : Fin d, ‖iteratedFDeriv ℝ r (Iteration.partialDeriv i u) x‖) *
        (∏ a, ‖v a‖) * ‖w‖ := by
      simp_rw [mul_assoc]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      ring

theorem derivativeProfile_succ_le_sum_partial [NeZero d] {Ω : Set E}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    derivativeProfile p Ω (r + 1) u ≤ derivativeProfile p Ω 0 u +
      ∑ i : Fin d, derivativeProfile p Ω r (Iteration.partialDeriv i u) := by
  classical
  have hbound (j : ℕ) :
      eLpNorm (fun x => ‖iteratedFDeriv ℝ (j + 1) u x‖) p (volume.restrict Ω) ≤
        ∑ i : Fin d, eLpNorm (fun x => ‖iteratedFDeriv ℝ j (Iteration.partialDeriv i u) x‖)
          p (volume.restrict Ω) := by
    have hnorm : eLpNorm (fun x => ‖iteratedFDeriv ℝ (j + 1) u x‖)
        p (volume.restrict Ω) ≤
        eLpNorm (fun x => ∑ i : Fin d,
          ‖iteratedFDeriv ℝ j (Iteration.partialDeriv i u) x‖) p (volume.restrict Ω) := by
      apply eLpNorm_mono_ae
      exact Filter.Eventually.of_forall fun x => by
        rw [norm_norm, Real.norm_eq_abs,
          abs_of_nonneg (Finset.sum_nonneg (fun i hi => norm_nonneg _))]
        exact norm_iteratedFDeriv_succ_le_sum_partial hu j x
    apply hnorm.trans
    have heq : (fun x => ∑ i : Fin d, ‖iteratedFDeriv ℝ j (Iteration.partialDeriv i u) x‖) =
        ∑ i : Fin d, (fun x => ‖iteratedFDeriv ℝ j (Iteration.partialDeriv i u) x‖) := by
      funext x
      rw [Finset.sum_apply]
    rw [heq]
    apply eLpNorm_sum_le _ hp
    intro i hi
    exact ((contDiff_partial hu i).continuous_iteratedFDeriv
      (by exact_mod_cast le_top)).norm.aestronglyMeasurable
  unfold derivativeProfile
  rw [Finset.sum_range_succ' (n := r + 1)]
  norm_num only [Finset.sum_range_one]
  apply (add_le_add (Finset.sum_le_sum (fun j hj => hbound j)) le_rfl).trans_eq
  rw [Finset.sum_comm, add_comm]

end Poincare.Analysis.Elliptic.InteriorEstimates
