import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.MorreyHigherOrder
import Mathlib.Analysis.Calculus.ContDiff.Bounds





noncomputable section

set_option maxHeartbeats 800000

open MeasureTheory Set
open scoped ENNReal
open Poincare.Analysis.Sobolev.Euclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)


def derivativeProfile (p : ℝ≥0∞) (Ω : Set E) (k : ℕ) (u : E → ℝ) : ℝ≥0∞ :=
  ∑ j ∈ Finset.range (k + 1),
    eLpNorm (fun x => ‖iteratedFDeriv ℝ j u x‖) p (volume.restrict Ω)

theorem derivativeProfile_ne_top [NeZero d] {p : ℝ} (_hp : 0 < p)
    {x₀ : E} {R : ℝ} (_hR : 0 < R) (k : ℕ)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    derivativeProfile (ENNReal.ofReal p) (Metric.ball x₀ R) k u ≠ ⊤ := by
  apply ENNReal.sum_ne_top.mpr
  intro j hj
  have hcont : Continuous (fun x => ‖iteratedFDeriv ℝ j u x‖) :=
    (hu.continuous_iteratedFDeriv (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).norm
  obtain ⟨A, hA⟩ := (isCompact_closedBall x₀ R).exists_bound_of_continuousOn
    hcont.continuousOn
  have : IsFiniteMeasure (volume.restrict (Metric.ball x₀ R)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
  apply MemLp.eLpNorm_ne_top
  apply MemLp.of_le_mul (g := fun _ : E => (1 : ℝ)) (c := A) (memLp_const 1)
    hcont.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simpa using hA x (Metric.ball_subset_closedBall hx)

theorem norm_iteratedFDeriv_iterClassicalPartial_le (n : ℕ) :
    ∀ (j : ℕ) (α : Fin n → Fin d) {u : E → ℝ},
      ContDiff ℝ (⊤ : ℕ∞) u → ∀ x,
        ‖iteratedFDeriv ℝ j (iterClassicalPartial n α u) x‖ ≤
          ‖iteratedFDeriv ℝ (j + n) u x‖ := by
  induction n with
  | zero => intro j α u hu x; simp
  | succ n ih =>
      intro j α u hu x
      rw [iterClassicalPartial_succ]
      have h := (ih j (fun i => α i.succ) (contDiff_partial_eta hu (α 0)) x).trans
        (norm_iteratedFDeriv_partial_le hu (α 0) (j + n) x)
      exact h.trans_eq (congrArg (fun r => ‖iteratedFDeriv ℝ r u x‖)
        (Nat.add_assoc j n 1))



theorem wkpNorm_le_derivativeProfile {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (k : ℕ)
    {u : E → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hc : HasCompactSupport u) (hs : tsupport u ⊆ Ω) :
    iteratedWeakSobolevNorm k p u Ω ≤
      (∑ j ∈ Finset.range (k + 1), (Fintype.card (Fin j → Fin d) : ℝ≥0∞)) *
        derivativeProfile p Ω k u := by
  classical
  unfold iteratedWeakSobolevNorm
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  calc
    ∑ α : Fin j → Fin d, eLpNorm (iterWeakPartial p j α u Ω) p (volume.restrict Ω) ≤
        ∑ _α : Fin j → Fin d, derivativeProfile p Ω k u := by
      apply Finset.sum_le_sum
      intro α hα
      rw [eLpNorm_congr_ae
        (iterWeakPartial_smooth_ae_eq_iterClassicalPartial hp hΩ j α hu hc hs)]
      calc
        eLpNorm (iterClassicalPartial j α u) p (volume.restrict Ω) ≤
            eLpNorm (fun x => ‖iteratedFDeriv ℝ j u x‖) p (volume.restrict Ω) := by
          apply eLpNorm_mono_ae (Filter.Eventually.of_forall fun x => ?_)
          have h := norm_iteratedFDeriv_iterClassicalPartial_le j 0 α hu x
          rw [norm_iteratedFDeriv_zero] at h
          rw [norm_norm]
          exact h.trans_eq (congrArg (fun r => ‖iteratedFDeriv ℝ r u x‖) (Nat.zero_add j))
        _ ≤ derivativeProfile p Ω k u := by
          unfold derivativeProfile
          exact Finset.single_le_sum
            (f := fun i => eLpNorm (fun x => ‖iteratedFDeriv ℝ i u x‖) p (volume.restrict Ω))
            (fun i hi => zero_le) hj
    _ = (Fintype.card (Fin j → Fin d) : ℝ≥0∞) * derivativeProfile p Ω k u := by
      simp [nsmul_eq_mul]


theorem derivativeProfile_mono_exponent {Ω : Set E} {p q : ℝ≥0∞}
    (hpq : p ≤ q) (k : ℕ) {u : E → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    derivativeProfile p Ω k u ≤ derivativeProfile q Ω k u *
      (volume.restrict Ω) univ ^ (1 / p.toReal - 1 / q.toReal) := by
  unfold derivativeProfile
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun j hj =>
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq
      (hu.continuous_iteratedFDeriv
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).norm.aestronglyMeasurable


def cutoffMultiplier (k : ℕ) (A : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), ∑ i ∈ Finset.range (j + 1), (j.choose i : ℝ) * A

theorem cutoffMultiplier_nonneg (k : ℕ) {A : ℝ} (hA : 0 ≤ A) :
    0 ≤ cutoffMultiplier k A := by
  exact Finset.sum_nonneg fun j hj => Finset.sum_nonneg fun i hi =>
    mul_nonneg (Nat.cast_nonneg _) hA



theorem derivativeProfile_mul_le {Ω : Set E} (hΩ : IsOpen Ω)
    {p : ℝ≥0∞} (hp : 1 ≤ p)
    (k : ℕ) {χ u : E → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    {A : ℝ} (hA : 0 ≤ A)
    (hbound : ∀ j ≤ k, ∀ x ∈ Ω, ‖iteratedFDeriv ℝ j χ x‖ ≤ A) :
    derivativeProfile p Ω k (fun x => χ x * u x) ≤
      ENNReal.ofReal (cutoffMultiplier k A) * derivativeProfile p Ω k u := by
  classical
  have hcoeff (j i : ℕ) : 0 ≤ (j.choose i : ℝ) * A :=
    mul_nonneg (Nat.cast_nonneg _) hA
  unfold derivativeProfile
  rw [cutoffMultiplier, ENNReal.ofReal_sum_of_nonneg
    (fun j hj => Finset.sum_nonneg fun i hi => hcoeff j i), Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => hcoeff j i), Finset.sum_mul]
  calc
    eLpNorm (fun x => ‖iteratedFDeriv ℝ j (fun x => χ x * u x) x‖)
        p (volume.restrict Ω) ≤
        eLpNorm (fun x => ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * A) * ‖iteratedFDeriv ℝ (j - i) u x‖)
          p (volume.restrict Ω) := by
      apply eLpNorm_mono_ae
      filter_upwards [ae_restrict_mem hΩ.measurableSet] with x hx
      rw [norm_norm, Real.norm_eq_abs, abs_of_nonneg
        (Finset.sum_nonneg fun i hi => mul_nonneg (hcoeff j i) (norm_nonneg _))]
      apply (norm_iteratedFDeriv_mul_le hχ hu x
        (by exact_mod_cast (le_top : (j : ℕ∞) ≤ ⊤))).trans
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := (Nat.le_of_lt_succ (Finset.mem_range.mp hi)).trans hjk
      gcongr
      exact hbound i hik x hx
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        eLpNorm (fun x => ((j.choose i : ℝ) * A) *
          ‖iteratedFDeriv ℝ (j - i) u x‖) p (volume.restrict Ω) := by
      have hmeas (i : ℕ) : AEStronglyMeasurable
          (fun x => ((j.choose i : ℝ) * A) * ‖iteratedFDeriv ℝ (j - i) u x‖)
          (volume.restrict Ω) := by
        have hle : ((j - i : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
          WithTop.coe_le_coe.mpr le_top
        exact (continuous_const.mul
          (hu.continuous_iteratedFDeriv hle).norm).aestronglyMeasurable
      have heq : (fun x => ∑ i ∈ Finset.range (j + 1),
          ((j.choose i : ℝ) * A) * ‖iteratedFDeriv ℝ (j - i) u x‖) =
          ∑ i ∈ Finset.range (j + 1),
            (fun x => ((j.choose i : ℝ) * A) * ‖iteratedFDeriv ℝ (j - i) u x‖) := by
        funext x
        rw [Finset.sum_apply]
      rw [heq]
      exact eLpNorm_sum_le (fun i hi => hmeas i) hp
    _ ≤ ∑ i ∈ Finset.range (j + 1), ENNReal.ofReal ((j.choose i : ℝ) * A) *
        ∑ n ∈ Finset.range (k + 1),
          eLpNorm (fun x => ‖iteratedFDeriv ℝ n u x‖) p (volume.restrict Ω) := by
      apply Finset.sum_le_sum
      intro i hi
      change eLpNorm (((j.choose i : ℝ) * A) •
        (fun x => ‖iteratedFDeriv ℝ (j - i) u x‖)) p (volume.restrict Ω) ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hcoeff j i)]
      gcongr
      exact Finset.single_le_sum
        (f := fun n => eLpNorm (fun x => ‖iteratedFDeriv ℝ n u x‖) p (volume.restrict Ω))
        (fun n hn => zero_le)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le j i).trans hjk)))

end Poincare.Analysis.Elliptic.InteriorEstimates
