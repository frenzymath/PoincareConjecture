import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.SupportedModulusEnergyVariation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeUniformizationEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.WeightedAnnulusEnergyIdentity
import Mathlib.Analysis.Calculus.LocalExtr.Basic

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {c0 c1 : ℝ → M}

theorem m64Annulus_supported_modulus_stationarity_of_minimum_of_eqOn
    (A : M64Annulus g c0 c1) {r : ℝ} (hr : 0 < r)
    (hminimum : A.area = m64LeastAnnulusArea g c0 c1)
    (hconformal : ∀ᵐ p ∂volume.restrict m64AnnulusDomain,
      r * m60AreaGram g A.map p 0 0 = r⁻¹ * m60AreaGram g A.map p 1 1 ∧
        m60AreaGram g A.map p 0 1 = 0)
    {v : ℝ × LoopPlane → M} {epsilon : ℝ} (hepsilon : 0 < epsilon)
    {O K : Set LoopPlane} (hO : IsOpen O) (hK : IsCompact K)
    (hKO : K ⊆ O) (hKdomain : K ⊆ m64AnnulusDomain)
    (hv : ContMDiffOn 𝓘(ℝ, ℝ × LoopPlane) (𝓡 n) ∞ v
      (Ioo (-epsilon) epsilon ×ˢ O))
    (hadmissible : ∀ s ∈ Ioo (-epsilon) epsilon,
      ∃ B : M64Annulus g c0 c1, EqOn B.map (fun p => v (s, p)) m64AnnulusDomain)
    (hcenter : ∀ p, v (0, p) = A.map p)
    (hfix : ∀ s ∈ Ioo (-epsilon) epsilon, ∀ z ∉ K,
      v (s, z) = v (0, z)) :
    HasDerivAt
      (fun s => ∫ p in m64AnnulusDomain,
        m64ModulusEnergyDensity g r (fun z => v (s, z)) p) 0 0 := by
  let E := fun s => ∫ p in m64AnnulusDomain,
    m64ModulusEnergyDensity g r (fun z => v (s, z)) p
  have hzero : (0 : ℝ) ∈ Ioo (-epsilon) epsilon := ⟨by linarith, hepsilon⟩
  have hmapzero : (fun z => v (0, z)) = A.map := funext hcenter
  have henergy0 : E 0 = A.area := by
    simp only [E, hmapzero]
    exact m64_weightedEnergy_eq_area_of_ae_modulus_conformal A hr hconformal
  have hint (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) :
      IntegrableOn (m64ModulusEnergyDensity g r (fun z => v (s, z)))
        m64AnnulusDomain volume := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    exact (B.weightedGramEnergy_integrable r).congr
      (m64ModulusEnergyDensity_ae_eq_of_eqOn g r hB)
  have hcomparison (s : ℝ) (hs : s ∈ Ioo (-epsilon) epsilon) : A.area ≤ E s := by
    obtain ⟨B, hB⟩ := hadmissible s hs
    have henergy : m64ClassicalWeightedGramEnergy g B r = E s :=
      integral_congr_ae (m64ModulusEnergyDensity_ae_eq_of_eqOn g r hB)
    calc
      A.area = m64LeastAnnulusArea g c0 c1 := hminimum
      _ ≤ B.area := m64LeastAnnulusArea_le_annulus B
      _ ≤ m64ClassicalWeightedGramEnergy g B r :=
        B.area_le_weightedGramEnergy hr (B.weightedGramEnergy_integrable r)
      _ = E s := henergy
  have hlocal : IsLocalMin E 0 := by
    filter_upwards [isOpen_Ioo.mem_nhds hzero] with s hs
    rw [henergy0]
    exact hcomparison s hs
  have hd := (m64ModulusEnergy_hasDerivAt_of_supported_variation g r hepsilon
    hO hK hKO hKdomain hv hfix hint).2
  have hdE : DifferentiableAt ℝ E 0 := hd.differentiableAt
  simpa only [hlocal.deriv_eq_zero] using hdE.hasDerivAt

end PoincareConjecture
