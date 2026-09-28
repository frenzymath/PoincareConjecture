import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2Profile
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Drift


noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_derivativeProfile_one_le_with_drift
    [NeZero d] {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : V ⊆ Ω) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    (c : Fin d → E → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) =
          ∫ x in V, (f x + ∑ i, c i x * partialDeriv i u x) * φ x) →
      derivativeProfile 2 W 1 u ≤ ENNReal.ofReal C *
        (derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f) := by
  obtain ⟨G, hG, hGbound⟩ := exists_gradient_integral_le_with_drift_on_nested_sets
    B hV hVΩ hW hWc hWV c hc
  refine ⟨1 + (d : ℝ) * Real.sqrt G, by positivity, ?_⟩
  intro u f hu hf heq
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hpW (i : Fin d) : MemLp (partialDeriv i u) 2 (volume.restrict W) :=
    (continuous_memLp_on_compact (contDiff_partial hu i).continuous hWc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  let A : ℝ≥0∞ := derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f
  have huBound : derivativeProfile 2 W 0 u ≤ A := by
    dsimp only [A]
    rw [derivativeProfile_zero, derivativeProfile_zero, derivativeProfile_zero]
    exact (eLpNorm_mono_measure u
      (Measure.restrict_mono (subset_closure.trans hWV) le_rfl)).trans le_self_add
  have hpartial (i : Fin d) : derivativeProfile 2 W 0 (partialDeriv i u) ≤
      ENNReal.ofReal (Real.sqrt G) * A := by
    dsimp only [A]
    rw [derivativeProfile_zero, derivativeProfile_zero, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hf (hpW i) hG
    have h := hGbound hu hum hf heq
    have hterm : (∫ x in W, (partialDeriv i u x) ^ 2) ≤
        ∫ x in W, ∑ j : Fin d, (partialDeriv j u x) ^ 2 := by
      apply integral_mono (hpW i).integrable_sq
        (integrable_finsetSum _ (fun j _ => (hpW j).integrable_sq))
      intro x
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (partialDeriv j u x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    linarith
  calc
    derivativeProfile 2 W 1 u ≤ derivativeProfile 2 W 0 u +
        ∑ i : Fin d, derivativeProfile 2 W 0 (partialDeriv i u) :=
      derivativeProfile_succ_le_sum_partial (by norm_num : (1 : ℝ≥0∞) ≤ 2) 0 hu
    _ ≤ A + ∑ _i : Fin d, (ENNReal.ofReal (Real.sqrt G) * A) :=
      add_le_add huBound (Finset.sum_le_sum (fun i _ => hpartial i))
    _ = ENNReal.ofReal (1 + (d : ℝ) * Real.sqrt G) * A := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_one, ENNReal.ofReal_natCast]
      ring

end Poincare.Analysis.Elliptic.InteriorEstimates
