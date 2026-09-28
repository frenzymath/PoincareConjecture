import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.H2
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2Profile

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_derivativeProfile_two_le_source
    [NeZero d] {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      derivativeProfile 2 W 2 u ≤ ENNReal.ofReal C *
        (derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f) := by
  obtain ⟨H, hH, hHbound⟩ := exists_h2_energy_le_source B hV hVc hVΩ hW hWc hWV
  refine ⟨((1 + d * (1 + d) : ℕ) : ℝ) * Real.sqrt H, by positivity, ?_⟩
  intro u f hu hf heq
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hlocal {g : E → ℝ} (hg : Continuous g) : MemLp g 2 (volume.restrict W) :=
    (continuous_memLp_on_compact hg hWc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have huW := hlocal hu.continuous
  have hpW (i : Fin d) := hlocal (contDiff_partial hu i).continuous
  have hppW (i k : Fin d) := hlocal (contDiff_partial (contDiff_partial hu i) k).continuous
  have hgradientInt : Integrable (fun x => ∑ i : Fin d, (partialDeriv i u x) ^ 2)
      (volume.restrict W) := integrable_finsetSum _ (fun i _ => (hpW i).integrable_sq)
  have hhessianInt : Integrable
      (fun x => ∑ k : Fin d, ∑ i : Fin d, (partialDeriv k (partialDeriv i u) x) ^ 2)
      (volume.restrict W) :=
    integrable_finsetSum _ (fun k _ => integrable_finsetSum _
      (fun i _ => (hppW i k).integrable_sq))
  have henergy := hHbound hu hf heq
  have huNonneg : 0 ≤ ∫ x in W, u x ^ 2 := integral_nonneg (fun x => sq_nonneg (u x))
  have hpNonneg : 0 ≤ ∫ x in W, ∑ i : Fin d, (partialDeriv i u x) ^ 2 :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun i _ => sq_nonneg _))
  have hppNonneg : 0 ≤ ∫ x in W, ∑ k : Fin d, ∑ i : Fin d,
      (partialDeriv k (partialDeriv i u) x) ^ 2 :=
    integral_nonneg (fun x => Finset.sum_nonneg (fun k _ =>
      Finset.sum_nonneg (fun i _ => sq_nonneg _)))
  let T : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt H) *
    (derivativeProfile 2 V 0 u + derivativeProfile 2 V 0 f)
  have huBound : derivativeProfile 2 W 0 u ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hf huW hH
    linarith
  have hpBound (i : Fin d) : derivativeProfile 2 W 0 (partialDeriv i u) ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hf (hpW i) hH
    have hterm : (∫ x in W, (partialDeriv i u x) ^ 2) ≤
        ∫ x in W, ∑ j : Fin d, (partialDeriv j u x) ^ 2 := by
      apply integral_mono (hpW i).integrable_sq hgradientInt
      intro x
      exact Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (partialDeriv j u x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    linarith
  have hppBound (i k : Fin d) :
      derivativeProfile 2 W 0 (partialDeriv k (partialDeriv i u)) ≤ T := by
    simp only [T, derivativeProfile_zero]
    apply eLpNorm_two_le_of_integral_sq_le_source hum hf (hppW i k) hH
    have hterm : (∫ x in W, (partialDeriv k (partialDeriv i u) x) ^ 2) ≤
        ∫ x in W, ∑ l : Fin d, ∑ j : Fin d, (partialDeriv l (partialDeriv j u) x) ^ 2 := by
      apply integral_mono (hppW i k).integrable_sq hhessianInt
      intro x
      have hi := Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin d => (partialDeriv k (partialDeriv j u) x) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      have hk := Finset.single_le_sum (s := Finset.univ)
        (f := fun l : Fin d => ∑ j : Fin d, (partialDeriv l (partialDeriv j u) x) ^ 2)
        (fun l _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ k)
      simpa only [Finset.sum_apply] using hi.trans hk
    linarith
  have hpOne (i : Fin d) :
      derivativeProfile 2 W 1 (partialDeriv i u) ≤ T + ∑ _k : Fin d, T := by
    apply (derivativeProfile_succ_le_sum_partial (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      0 (contDiff_partial hu i)).trans
    exact add_le_add (hpBound i) (Finset.sum_le_sum (fun k _ => hppBound i k))
  calc
    derivativeProfile 2 W 2 u ≤ derivativeProfile 2 W 0 u +
        ∑ i : Fin d, derivativeProfile 2 W 1 (partialDeriv i u) :=
      derivativeProfile_succ_le_sum_partial (by norm_num : (1 : ℝ≥0∞) ≤ 2) 1 hu
    _ ≤ T + ∑ _i : Fin d, (T + ∑ _k : Fin d, T) :=
      add_le_add huBound (Finset.sum_le_sum (fun i _ => hpOne i))
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, T,
        ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
      push_cast
      ring

end Poincare.Analysis.Elliptic.InteriorEstimates
