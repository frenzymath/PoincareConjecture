import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Localization
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Caccioppoli

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Elliptic.Iteration

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem exists_hessian_integral_le_source
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      (∫ x in W, ∑ k : Fin d, ∑ i : Fin d, (partialDeriv k (partialDeriv i u) x) ^ 2) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨U, hU, hWU, hUV⟩ := hWc.exists_isOpen_closure_subset (hV.mem_nhdsSet.mpr hWV)
  have hUc : IsCompact (closure U) :=
    hVc.of_isClosed_subset isClosed_closure (hUV.trans subset_closure)
  have hUΩ : closure U ⊆ Ω := hUV.trans (subset_closure.trans hVΩ)
  obtain ⟨H, hH, hHbound⟩ := exists_hessian_integral_le_of_weakEquation
    B hU hUc hUΩ hW hWc hWU
  obtain ⟨G, hG, hGbound⟩ := exists_gradient_integral_le_on_nested_sets
    B hV (subset_closure.trans hVΩ) hU hUc hUV
  refine ⟨H * (G + 1), mul_nonneg hH (by positivity), ?_⟩
  intro u f hu hf heq
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have hfU := hf.mono_measure (Measure.restrict_mono (subset_closure.trans hUV) le_rfl)
  have heqU := principal_equation_restrict B hU (subset_closure.trans hUV) heq
  have hsecond := hHbound hu hfU heqU
  have hfirst := hGbound hu hum hf heq
  have huMono : (∫ x in U, u x ^ 2) ≤ ∫ x in V, u x ^ 2 :=
    setIntegral_mono_set hum.integrable_sq
      (Eventually.of_forall (fun x => sq_nonneg (u x)))
      (Eventually.of_forall (subset_closure.trans hUV))
  have hfMono : (∫ x in U, f x ^ 2) ≤ ∫ x in V, f x ^ 2 :=
    setIntegral_mono_set hf.integrable_sq
      (Eventually.of_forall (fun x => sq_nonneg (f x)))
      (Eventually.of_forall (subset_closure.trans hUV))
  apply hsecond.trans
  calc
    _ ≤ H * (G * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) +
        (∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ hH
      exact add_le_add (add_le_add hfirst huMono) hfMono
    _ = _ := by ring

theorem exists_h2_energy_le_source
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVc : IsCompact (closure V)) (hVΩ : closure V ⊆ Ω)
    (hW : IsOpen W) (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      ((∫ x in W, u x ^ 2) +
        (∫ x in W, ∑ i : Fin d, (partialDeriv i u x) ^ 2) +
        (∫ x in W, ∑ k : Fin d, ∑ i : Fin d, (partialDeriv k (partialDeriv i u) x) ^ 2)) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨H, hH, hHbound⟩ := exists_hessian_integral_le_source B hV hVc hVΩ hW hWc hWV
  obtain ⟨G, hG, hGbound⟩ := exists_gradient_integral_le_on_nested_sets
    B hV (subset_closure.trans hVΩ) hW hWc hWV
  refine ⟨1 + G + H, by positivity, ?_⟩
  intro u f hu hf heq
  have hum : MemLp u 2 (volume.restrict V) :=
    (continuous_memLp_on_compact hu.continuous hVc).mono_measure
      (Measure.restrict_mono subset_closure le_rfl)
  have huMono : (∫ x in W, u x ^ 2) ≤ ∫ x in V, u x ^ 2 :=
    setIntegral_mono_set hum.integrable_sq
      (Eventually.of_forall (fun x => sq_nonneg (u x)))
      (Eventually.of_forall (subset_closure.trans hWV))
  have hfnonneg : 0 ≤ ∫ x in V, f x ^ 2 := integral_nonneg (fun x => sq_nonneg (f x))
  have hfirst := hGbound hu hum hf heq
  have hsecond := hHbound hu hf heq
  dsimp [partialDeriv] at hsecond ⊢
  nlinarith

end Poincare.Analysis.Elliptic.InteriorEstimates
