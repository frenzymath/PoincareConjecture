import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.Boundary.Embedding.Subcritical








set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace Poincare.Analysis.Sobolev.BoundaryEmbedding

open Weak BoundaryTangential Poincare.Analysis.Sobolev.Euclidean
open EuclideanEmbedding

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

private theorem tower_to_supercritical (s : ℕ) {p : ℝ} (hp : 1 ≤ p)
    (hreg : RegularExponent.IsRegular (d : ℝ) p (s + 1))
    (hdp : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p)
    {u : E → ℝ} (hc : HasCompactSupport u)
    (hu : MemWkp (1 + s) (ENNReal.ofReal p) u (halfSpace d)) :
    ∃ q : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧ MemWkp 1 (ENNReal.ofReal q) u (halfSpace d) := by
  induction s generalizing p u with
  | zero => exact ⟨p, hp, by simpa using hdp, by simpa using hu⟩
  | succ s ih =>
    have hp_ne : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
    rcases lt_or_gt_of_ne hp_ne with hplt | hpgt
    · have hu' : MemWkp ((s + 1) + 1) (ENNReal.ofReal p) u (halfSpace d) := by
        simpa only [Nat.add_comm 1] using hu
      have hv := memWkp_subcritical (s + 1) hp hplt hc hu'
      have hq : 1 ≤ (d : ℝ) * p / ((d : ℝ) - p) := by
        simpa only [TowerStep.pOne] using TowerStep.pOne_ge_one hp hplt
      have hregq : RegularExponent.IsRegular (d : ℝ)
          ((d : ℝ) * p / ((d : ℝ) - p)) (s + 1) := hreg.tower_step hp hplt
      have hdpq : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * ((d : ℝ) * p / ((d : ℝ) - p)) :=
        IterationCalc.kp1_real_gt_d_of_kp1p_gt_d d (s + 1) p (by linarith) hplt
          (by simpa only [Nat.cast_add, Nat.cast_one] using hdp)
      exact ih hq hregq hdpq hc (by simpa only [Nat.add_comm 1, halfSpace] using hv)
    · exact ⟨p, hp, hpgt, MemWkp.le_of_le (by omega) hu⟩



theorem exists_supercritical_memW1p {u : E → ℝ} (hc : HasCompactSupport u)
    (hu : MemWkp (d + 1) 2 u {x : E | 0 < x 0}) :
    ∃ p : ℝ, 1 ≤ p ∧ (d : ℝ) < p ∧
      MemW1p (ENNReal.ofReal p) u {x : E | 0 < x 0} := by
  have hdp2 : (d : ℝ) < ((d + 1 : ℕ) : ℝ) * 2 := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨p, hp, hp2, hdp, hreg⟩ := RegularExponent.exists_regular_exponent_below
    (d : ℝ) (d + 1) (by omega) (by norm_num : (1 : ℝ) < 2) hdp2
  have hpe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  have hpe2 : ENNReal.ofReal p ≤ (2 : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal hp2.le
  have hup : MemWkp (d + 1) (ENNReal.ofReal p) u (halfSpace d) :=
    EuclideanIteratedMonoExp.memWkp_mono_exponent_of_tsupport_subset (d + 1)
      isOpen_halfSpace (isClosed_tsupport u) hc.measure_lt_top.ne hpe hpe2 (subset_refl _) hu
  obtain ⟨q, hq, hdq, huq⟩ := tower_to_supercritical d hp hreg hdp hc
    (by simpa only [Nat.add_comm 1] using hup)
  exact ⟨q, hq, hdq, huq.memW1p⟩

end Poincare.Analysis.Sobolev.BoundaryEmbedding
