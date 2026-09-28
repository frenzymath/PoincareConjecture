import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy














set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




structure M64FreeMorreyUniformizationCandidate
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M)
    (A : M64Annulus g c0 c1) (ε : ℝ) where
  modulus : ℝ
  modulus_pos : 0 < modulus
  sigma0 : M64PeriodicDegreeOneLift
  sigma1 : M64PeriodicDegreeOneLift
  annulus : M64Annulus g (c0 ∘ sigma0.map) (c1 ∘ sigma1.map)
  weighted_integrable : IntegrableOn (fun p =>
    (modulus * m60AreaGram g annulus.map p 0 0 +
      modulus⁻¹ * m60AreaGram g annulus.map p 1 1) / 2)
    m64AnnulusDomain volume
  ae_modulus_conformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
    modulus * m60AreaGram g annulus.map p 0 0 =
        modulus⁻¹ * m60AreaGram g annulus.map p 1 1 ∧
      m60AreaGram g annulus.map p 0 1 = 0
  energy_le : m64ClassicalWeightedGramEnergy g annulus modulus ≤ A.area + ε



theorem M64FreeMorreyUniformizationCandidate.weightedEnergy_eq_area
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    {A : M64Annulus g c0 c1} {ε : ℝ}
    (C : M64FreeMorreyUniformizationCandidate g c0 c1 A ε) :
    m64ClassicalWeightedGramEnergy g C.annulus C.modulus = C.annulus.area := by
  exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal C.annulus
    C.modulus_pos C.ae_modulus_conformal




structure M64FreeMorreyUniformizationCertificate
    (g : RiemannianMetric n M) (c0 c1 : ℝ → M) where
  candidate : ∀ A : M64Annulus g c0 c1, ∀ ε : ℝ, 0 < ε →
    M64FreeMorreyUniformizationCandidate g c0 c1 A ε



theorem m64FreeConformalModulusApproximation_of_morrey_certificate
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (C : M64FreeMorreyUniformizationCertificate g c0 c1) :
    M64FreeConformalModulusApproximation g c0 c1 := by
  intro A ε hε
  let W := C.candidate A ε hε
  exact ⟨W.modulus, W.modulus_pos, W.sigma0, W.sigma1, W.annulus,
    W.weighted_integrable, W.energy_le⟩

end PoincareConjecture
