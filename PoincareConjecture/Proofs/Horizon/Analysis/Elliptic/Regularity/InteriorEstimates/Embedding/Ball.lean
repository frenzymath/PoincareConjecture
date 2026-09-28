import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Cutoff
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Embedding.Tower









noncomputable section

open MeasureTheory Set Filter Metric
open scoped ENNReal Topology
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem smooth_jet_le_l2_derivativeProfile {x₀ : E} {R : ℝ} (hR : 0 < R) (m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : E → ℝ}, ContDiff ℝ (⊤ : ℕ∞) u →
      ∀ x ∈ Metric.ball x₀ (R / 2),
        ‖iteratedFDeriv ℝ m u x‖ ≤
          C * (derivativeProfile 2 (Metric.ball x₀ R) (m + 1 + d) u).toReal := by
  classical
  let Ω := Metric.ball x₀ R
  let k := m + 1 + d
  obtain ⟨χ, A, hχ, hχc, hχs, hχone, hA, hcutoff⟩ :=
    exists_fixed_cutoff_profile_bound hR k
  obtain ⟨p, hp, hp₂, hdp, hreg⟩ :=
    RegularExponent.exists_regular_exponent_below (d : ℝ) (d + 1)
      (by omega) (by norm_num : (1 : ℝ) < 2)
      (by push_cast; linarith [Nat.cast_nonneg (α := ℝ) d])
  obtain ⟨q, T, hq, hdq, hT, htower⟩ :=
    quantitative_sobolev_tower (Ω := Ω) isOpen_ball m d hp hreg hdp
  obtain ⟨B, hB, hmorrey⟩ :=
    Poincare.Analysis.Sobolev.EuclideanMorrey.smooth_morrey_iteratedFDeriv_bound_uniform
      hdq hR m
  let N : ℝ≥0∞ := ∑ j ∈ Finset.range (k + 1), (Fintype.card (Fin j → Fin d) : ℝ≥0∞)
  let V : ℝ≥0∞ := (volume.restrict Ω) univ ^
    (1 / (ENNReal.ofReal p).toReal - 1 / (2 : ℝ≥0∞).toReal)
  let Q : ℝ≥0∞ := ENNReal.ofReal T * N * V * ENNReal.ofReal A
  have hpenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa using ENNReal.ofReal_le_ofReal hp
  have hp₂enn : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal hp₂.le
  have hqenn : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq
  have hN : N ≠ ⊤ := ENNReal.sum_ne_top.mpr (fun j hj => ENNReal.natCast_ne_top _)
  have hV : V ≠ ⊤ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · rw [ENNReal.toReal_ofReal (lt_of_lt_of_le zero_lt_one hp).le]
      norm_num only [ENNReal.toReal_ofNat]
      exact sub_nonneg.mpr (one_div_le_one_div_of_le
        (lt_of_lt_of_le zero_lt_one hp) hp₂.le)
    · rw [Measure.restrict_apply_univ]
      exact measure_ball_lt_top.ne
  have hQ : Q ≠ ⊤ := ENNReal.mul_ne_top
    (ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hN) hV)
    ENNReal.ofReal_ne_top
  refine ⟨B * Q.toReal, mul_nonneg hB ENNReal.toReal_nonneg, ?_⟩
  intro u hu x hx
  let v : E → ℝ := fun y => χ y * u y
  have hv : ContDiff ℝ (⊤ : ℕ∞) v := hχ.mul hu
  have hvc : HasCompactSupport v := hχc.mul_right
  have hvs : tsupport v ⊆ Ω := tsupport_mul_subset_left.trans hχs
  have hvp : MemWkp k (ENNReal.ofReal p) v Ω :=
    MemWkp_of_smooth_compactSupport isOpen_ball hv hvc hvs hpenn k
  obtain ⟨hvq, hnormq⟩ := htower hvc hvs hvp
  have hprofile : derivativeProfile (ENNReal.ofReal q) Ω (m + 1) v ≤
      Q * derivativeProfile 2 Ω k u := by
    calc
      derivativeProfile (ENNReal.ofReal q) Ω (m + 1) v ≤
          iteratedWeakSobolevNorm (m + 1) (ENNReal.ofReal q) v Ω :=
        eLpNorm_iteratedFDeriv_le_wkpNorm isOpen_ball hqenn (m + 1) hv hvc hvs
      _ ≤ ENNReal.ofReal T * iteratedWeakSobolevNorm k (ENNReal.ofReal p) v Ω := hnormq
      _ ≤ ENNReal.ofReal T * (N * derivativeProfile (ENNReal.ofReal p) Ω k v) := by
        gcongr
        exact wkpNorm_le_derivativeProfile isOpen_ball hpenn k hv hvc hvs
      _ ≤ ENNReal.ofReal T * (N * (derivativeProfile 2 Ω k v * V)) := by
        gcongr
        exact derivativeProfile_mono_exponent hp₂enn k hv
      _ ≤ ENNReal.ofReal T * (N *
          ((ENNReal.ofReal A * derivativeProfile 2 Ω k u) * V)) := by
        gcongr
        exact hcutoff hu
      _ = Q * derivativeProfile 2 Ω k u := by dsimp [Q]; ring
  have hfinite : derivativeProfile 2 Ω k u ≠ ⊤ := by
    simpa using derivativeProfile_ne_top (by norm_num : (0 : ℝ) < 2) hR k hu
  have hprofileReal : (derivativeProfile (ENNReal.ofReal q) Ω (m + 1) v).toReal ≤
      Q.toReal * (derivativeProfile 2 Ω k u).toReal := by
    simpa only [ENNReal.toReal_mul] using
      ENNReal.toReal_mono (ENNReal.mul_ne_top hQ hfinite) hprofile
  have hsum : (derivativeProfile (ENNReal.ofReal q) Ω (m + 1) v).toReal =
      ∑ j ∈ Finset.range (m + 2),
        (eLpNorm (fun y => ‖iteratedFDeriv ℝ j v y‖)
          (ENNReal.ofReal q) (volume.restrict Ω)).toReal := by
    apply ENNReal.toReal_sum
    intro j hj
    exact (ENNReal.lt_top_of_sum_ne_top
      (derivativeProfile_ne_top (lt_of_lt_of_le zero_lt_one hq) hR (m + 1) hv) hj).ne
  have heq : v =ᶠ[𝓝 x] u := by
    filter_upwards [isOpen_ball.mem_nhds hx] with y hy
    simp only [v, hχone hy, one_mul]
  have hjet : iteratedFDeriv ℝ m v x = iteratedFDeriv ℝ m u x :=
    (heq.iteratedFDeriv ℝ m).eq_of_nhds
  have hm := hmorrey hv x hx
  rw [hjet, ← hsum] at hm
  exact hm.trans ((mul_le_mul_of_nonneg_left hprofileReal hB).trans_eq (mul_assoc _ _ _).symm)

end Poincare.Analysis.Elliptic.InteriorEstimates
