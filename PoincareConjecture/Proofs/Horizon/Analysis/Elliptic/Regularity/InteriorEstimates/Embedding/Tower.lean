import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.ExponentIteration








noncomputable section

open MeasureTheory Set
open scoped ENNReal
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.EuclideanEmbedding

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)



theorem quantitative_sobolev_tower {Ω : Set E} (hΩ : IsOpen Ω) (m s : ℕ)
    {p : ℝ} (hp : 1 ≤ p)
    (hreg : RegularExponent.IsRegular (d : ℝ) p (s + 1))
    (hdp : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p) :
    ∃ q C : ℝ, 1 ≤ q ∧ (d : ℝ) < q ∧ 0 ≤ C ∧
      ∀ {f : E → ℝ}, HasCompactSupport f → tsupport f ⊆ Ω →
        MemWkp (m + 1 + s) (ENNReal.ofReal p) f Ω →
          MemWkp (m + 1) (ENNReal.ofReal q) f Ω ∧
          iteratedWeakSobolevNorm (m + 1) (ENNReal.ofReal q) f Ω ≤
            ENNReal.ofReal C *
              iteratedWeakSobolevNorm (m + 1 + s) (ENNReal.ofReal p) f Ω := by
  induction s generalizing p with
  | zero =>
      have hd : (d : ℝ) < p := by simpa using hdp
      refine ⟨p, 1, hp, hd, by norm_num, ?_⟩
      intro f hf hs hmem
      simpa using And.intro hmem (le_refl
        (iteratedWeakSobolevNorm (m + 1) (ENNReal.ofReal p) f Ω))
  | succ s ih =>
      have hpne : p ≠ (d : ℝ) := hreg.p_ne_n_of_one_le (by omega)
      rcases lt_or_gt_of_ne hpne with hplt | hpgt
      · let p₁ : ℝ := TowerStep.pOne d p
        have hp₁ : 1 ≤ p₁ := TowerStep.pOne_ge_one hp hplt
        have hreg₁ : RegularExponent.IsRegular (d : ℝ) p₁ (s + 1) :=
          hreg.tower_step hp hplt
        have hdp₁ : (d : ℝ) < ((s + 1 : ℕ) : ℝ) * p₁ := by
          apply IterationCalc.kp1_real_gt_d_of_kp1p_gt_d d (s + 1) p
            (lt_of_lt_of_le zero_lt_one hp) hplt
          simpa only [Nat.cast_add, Nat.cast_one] using hdp
        obtain ⟨q, C, hq, hdq, hC, hbound⟩ := ih hp₁ hreg₁ hdp₁
        let A := TowerStep.subcriticalConstant (m + 1 + s) d p
        have hA : 0 ≤ A := TowerStep.subcriticalConstant_nonneg _ _ _
        refine ⟨q, C * A, hq, hdq, mul_nonneg hC hA, ?_⟩
        intro f hf hs hmem
        have hmem' : MemWkp ((m + 1 + s) + 1) (ENNReal.ofReal p) f Ω := by
          simpa only [Nat.add_assoc] using hmem
        obtain ⟨hnext, hnextbound⟩ := TowerStep.MemWkp_subcritical_iterated
          (m + 1 + s) hp hplt hΩ hf hs hmem'
        obtain ⟨hfinal, hfinalbound⟩ := hbound hf hs hnext
        refine ⟨hfinal, hfinalbound.trans ?_⟩
        calc
          ENNReal.ofReal C * iteratedWeakSobolevNorm (m + 1 + s)
              (ENNReal.ofReal p₁) f Ω ≤
              ENNReal.ofReal C * (ENNReal.ofReal A *
                iteratedWeakSobolevNorm ((m + 1 + s) + 1)
                  (ENNReal.ofReal p) f Ω) := by gcongr
          _ = ENNReal.ofReal (C * A) *
              iteratedWeakSobolevNorm (m + 1 + (s + 1))
                (ENNReal.ofReal p) f Ω := by
            rw [ENNReal.ofReal_mul hC, mul_assoc]
            simp only [Nat.add_assoc]
      · refine ⟨p, 1, hp, hpgt, by norm_num, ?_⟩
        intro f hf hs hmem
        refine ⟨hmem.le_of_le (by omega), ?_⟩
        simpa using EuclideanIterated.wkpNorm_mono_order (d := d)
          (f := f) (Ω := Ω) (p := ENNReal.ofReal p)
          (show m + 1 ≤ m + 1 + (s + 1) by omega)

end Poincare.Analysis.Elliptic.InteriorEstimates
