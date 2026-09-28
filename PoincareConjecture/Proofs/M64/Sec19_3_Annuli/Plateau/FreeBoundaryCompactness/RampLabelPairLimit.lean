import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.RampLabelGlobalLimit
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.ReflectionEnergy

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

theorem free_ramp_labels_continuous_limit
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t) (hramp1 : M63IsRampAt P gamma1 t)
    {lo hi : ℝ} (hlo : 0 < lo) (sigma0 sigma1 : ℕ → M64PeriodicDegreeOneLift)
    (A : ∀ j, M64Annulus (P.flow.metric t)
      (gamma0 ∘ (sigma0 j).map) (gamma1 ∘ (sigma1 j).map))
    (hA : ∀ j, ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 (A j).map Strip)
    (r : ℕ → ℝ) (hr : ∀ j, r j ∈ Icc lo hi)
    (hE : ∀ j, IntegrableOn (fun p =>
      (r j * m60AreaGram (P.flow.metric t) (A j).map p 0 0 +
        (r j)⁻¹ * m60AreaGram (P.flow.metric t) (A j).map p 1 1) / 2) m64AnnulusDomain)
    (K : ℝ) (hK : ∀ j, m64ClassicalWeightedGramEnergy (P.flow.metric t) (A j) (r j) ≤ K) :
    ∃ (k : ℕ → ℕ) (L0 L1 : ℝ → ℝ), StrictMono k ∧ Continuous L0 ∧ Continuous L1 ∧
      Monotone L0 ∧ Monotone L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + curvePeriod) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + curvePeriod) ∧
      L0 0 ∈ Icc (0 : ℝ) curvePeriod ∧ L1 0 ∈ Icc (0 : ℝ) curvePeriod ∧
      (∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma0 (k j))).map x)
        atTop (𝓝 (L0 x))) ∧
      ∀ x, Tendsto (fun j => (normalizedDegreeOneLift (sigma1 (k j))).map x)
        atTop (𝓝 (L1 x)) := by
  obtain ⟨k0, L0, hk0, hc0, hm0, hp0, h00, hlim0⟩ :=
    free_ramp_lower_labels_continuous_limit P t gamma0 hgamma0 hperiod0 hramp0
      hlo sigma0 (fun j => gamma1 ∘ (sigma1 j).map) A hA r hr hE K hK
  have hrevE (j : ℕ) := annulus_reverse_weightedGram_integrable (A (k0 j))
    (r (k0 j)) (hE (k0 j))
  have hrevK (j : ℕ) : m64ClassicalWeightedGramEnergy (P.flow.metric t)
      (m64Annulus_reverse (A (k0 j))) (r (k0 j)) ≤ K := by
    rw [annulus_reverse_weightedGramEnergy]
    exact hK (k0 j)
  obtain ⟨k1, L1, hk1, hc1, hm1, hp1, h10, hlim1⟩ :=
    free_ramp_lower_labels_continuous_limit P t gamma1 hgamma1 hperiod1 hramp1
      hlo (fun j => sigma1 (k0 j)) (fun j => gamma0 ∘ (sigma0 (k0 j)).map)
      (fun j => m64Annulus_reverse (A (k0 j)))
      (fun j => annulus_reverse_contMDiffOn_strip (A (k0 j)) (hA (k0 j)))
      (fun j => r (k0 j)) (fun j => hr (k0 j)) hrevE K hrevK
  exact ⟨k0 ∘ k1, L0, L1, hk0.comp hk1, hc0, hc1, hm0, hm1, hp0, hp1, h00, h10,
    fun x => (hlim0 x).comp hk1.tendsto_atTop, hlim1⟩

end PoincareConjecture.M64
