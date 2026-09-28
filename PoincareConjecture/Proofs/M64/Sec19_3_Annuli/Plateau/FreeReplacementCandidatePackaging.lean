import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationCertificate
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeReplacementAdmissionOwnSeed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture

universe u

variable {n m : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M]
  [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin m)

theorem m64FreeReplacement_candidate_of_own_admission
    {g : RiemannianMetric n M} {c0 c1 : ℝ → M}
    (A0 : M64Annulus g c0 c1) {eps : ℝ}
    (sigma0 sigma1 : M64PeriodicDegreeOneLift)
    {f : LoopPlane → M} {U : Set LoopPlane}
    (hU : IsOpen U) (hdom : m64AnnulusDomain ⊆ U)
    (hf : ContMDiffOn (𝓡 2) (𝓡 n) 1 f U)
    (hperiodic : ∀ x s : ℝ,
      f (annulusPoint (x + curvePeriod) s) = f (annulusPoint x s))
    (hlower : ∀ x, f (annulusPoint x 0) = c0 (sigma0.map x))
    (hupper : ∀ x, f (annulusPoint x 1) = c1 (sigma1.map x))
    {r : ℝ} (hr : 0 < r)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g f p 0 0 = r⁻¹ * m60AreaGram g f p 1 1 ∧
        m60AreaGram g f p 0 1 = 0)
    (henergy : (∫ p in m64AnnulusDomain,
        (r * m60AreaGram g f p 0 0 +
          r⁻¹ * m60AreaGram g f p 1 1) / 2) ≤ A0.area + eps)
    (e : M → E) (he : ContMDiff (𝓡 n) (𝓡 m) 1 e) :
    ∃ C : M64FreeMorreyUniformizationCandidate g c0 c1 A0 eps,
      C.modulus = r ∧ C.sigma0 = sigma0 ∧ C.sigma1 = sigma1 ∧
      C.annulus.map = f ∧
      ∃ W : M64ObservedWeakAnnulus (n := n) e
          (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        W.map = f ∧
          ∀ i, ∀ᵐ p ∂volume.restrict (interior m64AnnulusDomain),
            W.column i p =
              fderiv ℝ (e ∘ f) p (EuclideanSpace.single i 1) := by
  obtain ⟨A, hA, W, hW, hcolumns⟩ :=
    m64FreeReplacement_admit_ownObservedSeed
      (g := g) (c0 := c0 ∘ sigma0.map) (c1 := c1 ∘ sigma1.map)
      hU hdom hf hperiodic hlower hupper e he
  have hconformalA : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0 := by
    filter_upwards [hconformal] with p hp
    simpa only [hA] using hp
  have henergyA : m64ClassicalWeightedGramEnergy g A r ≤ A0.area + eps := by
    unfold m64ClassicalWeightedGramEnergy
    simpa only [hA] using henergy
  let C : M64FreeMorreyUniformizationCandidate g c0 c1 A0 eps := {
    modulus := r
    modulus_pos := hr
    sigma0 := sigma0
    sigma1 := sigma1
    annulus := A
    weighted_integrable := A.weightedGramEnergy_integrable r
    ae_modulus_conformal := hconformalA
    energy_le := henergyA }
  refine ⟨C, rfl, rfl, rfl, ?_, W, ?_, hcolumns⟩
  · simp only [C, hA]
  · simpa only [hA] using hW

end PoincareConjecture
