import PoincareConjecture.Proofs.M07.Analysis.Calculus.SmoothCompactness.FiniteDimensional
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.Overlap.Distance

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology NNReal

universe u

namespace PoincareConjecture.M47

open Poincare.Analysis.Calculus

theorem terminalGerms_extract_common_charts
    {M : ℕ → Type u} [∀ k, PseudoMetricSpace (M k)]
    (U : ℕ → Set (EuclideanSpace ℝ (Fin 3))) (hU : ∀ i, IsOpen (U i))
    (tau : ℕ → ℝ)
    (e : ∀ k i, U i → M k) (L : ℕ → ℝ≥0)
    (he : ∀ k i, LipschitzWith (L i) (e k i))
    (hdistance : ∀ i j (x : U i) (y : U j), ∃ C : ℝ,
      ∀ k, dist (e k i x) (e k j y) ≤ C)
    (f0 : ℕ → ℕ → EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hf0 : ∀ i k, ContDiffOn ℝ ∞ (f0 i k) (U i))
    (hbound0 : ∀ i K, IsCompact K → K ⊆ U i → ∀ m : ℕ, ∃ C : ℝ,
      ∀ᶠ k in atTop, ∀ x ∈ K, ‖iteratedFDeriv ℝ m (f0 i k) x‖ ≤ C)
    (fminus : ℕ → ℕ → ℝ × EuclideanSpace ℝ (Fin 3) →
      EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ)
    (hfminus : ∀ i k, ContDiffOn ℝ ∞ (fminus i k) (Ioo (-tau i) 0 ×ˢ U i))
    (hboundMinus : ∀ i K, IsCompact K → K ⊆ Ioo (-tau i) 0 ×ˢ U i →
      ∀ m : ℕ, ∃ C : ℝ, ∀ᶠ k in atTop, ∀ p ∈ K,
        ‖iteratedFDeriv ℝ m (fminus i k) p‖ ≤ C) :
    ∃ sigma : ℕ → ℕ, StrictMono sigma ∧
      ∃ B0 : ℕ → EuclideanSpace ℝ (Fin 3) →
          EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
        (∀ i, ContDiffOn ℝ ∞ (B0 i) (U i)) ∧
        (∀ i m K, IsCompact K → K ⊆ U i → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m (f0 i (sigma k)))
          (iteratedFDeriv ℝ m (B0 i)) atTop K) ∧
        ∃ Bminus : ℕ → ℝ × EuclideanSpace ℝ (Fin 3) →
            EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ,
          (∀ i, ContDiffOn ℝ ∞ (Bminus i) (Ioo (-tau i) 0 ×ˢ U i)) ∧
          (∀ i m K, IsCompact K → K ⊆ Ioo (-tau i) 0 ×ˢ U i →
            TendstoUniformlyOn (fun k => iteratedFDeriv ℝ m (fminus i (sigma k)))
              (iteratedFDeriv ℝ m (Bminus i)) atTop K) ∧
          ∃ D : ∀ i j, C(U i × U j, ℝ), ∀ i j,
            TendstoLocallyUniformly
              (fun k (p : U i × U j) => dist (e (sigma k) i p.1) (e (sigma k) j p.2))
              (D i j) atTop := by
  let : ∀ i, LocallyCompactSpace (U i) := fun i => (hU i).locallyCompactSpace
  obtain ⟨sigma0, hsigma0, B0, hB0, hjet0⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional hU f0 hf0 hbound0
  obtain ⟨sigma1, hsigma1, Bminus, hBminus, hjetMinus⟩ :=
    exists_common_smoothSubsequenceExtraction_finiteDimensional
      (fun i => isOpen_Ioo.prod (hU i))
      (fun i k => fminus i (sigma0 k)) (fun i k => hfminus i (sigma0 k)) (by
        intro i K hK hKU m
        obtain ⟨C, hC⟩ := hboundMinus i K hK hKU m
        exact ⟨C, hsigma0.tendsto_atTop.eventually hC⟩)
  obtain ⟨sigma2, hsigma2, D, hD⟩ := ChartDistance.exists_pairwise_limits
    (fun k => e (sigma0 (sigma1 k))) L (fun k => he (sigma0 (sigma1 k))) (by
      intro i j x y
      obtain ⟨C, hC⟩ := hdistance i j x y
      exact ⟨C, fun k => hC (sigma0 (sigma1 k))⟩)
  let sigma := sigma0 ∘ sigma1 ∘ sigma2
  refine ⟨sigma, hsigma0.comp (hsigma1.comp hsigma2), B0, hB0, ?_,
    Bminus, hBminus, ?_, D, hD⟩
  · intro i m K hK hKU V hV
    exact (hsigma1.comp hsigma2).tendsto_atTop.eventually (hjet0 i m K hK hKU V hV)
  · intro i m K hK hKU V hV
    exact hsigma2.tendsto_atTop.eventually (hjetMinus i m K hK hKU V hV)

end PoincareConjecture.M47
