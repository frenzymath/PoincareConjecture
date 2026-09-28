import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusPhaseEnergy
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusBoundarySeparation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Uniformization.ScalarFreeModulusApproximation

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

local notation "Strip" => Set.preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)

theorem free_ramp_approximation_confined_of_disjoint_images
    (P : M62.CircleProductData F circumference) (t : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hperiod0 : Function.Periodic gamma0 curvePeriod)
    (hperiod1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 t)
    (hdisjoint : Disjoint (range gamma0) (range gamma1))
    (A0 : M64Annulus (P.flow.metric t) gamma0 gamma1) :
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ eps : ℝ, 0 < eps →
      ∃ r : ℝ, r ∈ Icc lo hi ∧
      ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
        (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
        ∃ B : M64Annulus (P.flow.metric t) (gamma0 ∘ sigma0.map) (gamma1 ∘ sigma1.map),
          ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 B.map Strip ∧
          IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) B.map p 0 0 +
            r⁻¹ * m60AreaGram (P.flow.metric t) B.map p 1 1) / 2) m64AnnulusDomain ∧
          m64ClassicalWeightedGramEnergy (P.flow.metric t) B r <
            m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + eps := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  have h0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma0 := hgamma0.of_le (by norm_num)
  have h1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 1 gamma1 := hgamma1.of_le (by norm_num)
  obtain ⟨beta, hbeta, hlower⟩ := free_annulus_inverse_modulus_bound_of_disjoint_images
    (P.flow.metric t) h0 h1 hperiod0 hperiod1 hdisjoint
  let level := m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + 1
  have hlevel : 0 < level := by
    dsimp [level]
    linarith [m64LeastAnnulusArea_nonneg A0]
  let lo := beta / level
  let hi := (2 * curvePeriod * level) / circumference ^ 2
  have hlo : 0 < lo := div_pos hbeta hlevel
  have hchoose (eps : ℝ) (heps : 0 < eps) :
      ∃ r : ℝ, r ∈ Icc lo hi ∧
      ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
        (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
        ∃ B : M64Annulus (P.flow.metric t) (gamma0 ∘ sigma0.map) (gamma1 ∘ sigma1.map),
          ContMDiffOn (𝓡 2) (𝓡 (n + 1)) 1 B.map Strip ∧
          IntegrableOn (fun p => (r * m60AreaGram (P.flow.metric t) B.map p 0 0 +
            r⁻¹ * m60AreaGram (P.flow.metric t) B.map p 1 1) / 2) m64AnnulusDomain ∧
          m64ClassicalWeightedGramEnergy (P.flow.metric t) B r <
            m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + eps := by
    have hdelta : 0 < min eps 1 := lt_min heps zero_lt_one
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer A0 (half_pos hdelta)
    obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, hBE⟩ :=
      M64Uniformization.exists_free_annulus_energy_lt_area A h0 h1 (half_pos hdelta)
    have hE : m64ClassicalWeightedGramEnergy (P.flow.metric t) B r <
        m64LeastAnnulusArea (P.flow.metric t) gamma0 gamma1 + min eps 1 := by linarith
    have hbelow : m64ClassicalWeightedGramEnergy (P.flow.metric t) B r < level :=
      hE.trans_le (add_le_add le_rfl (min_le_right eps 1))
    have hl : lo ≤ r := by
      apply (div_le_iff₀ hlevel).mpr
      have hbetaE := (hlower sigma0 sigma1 hs0 hs1 B r hr).trans hbelow.le
      have hh := mul_le_mul_of_nonneg_right hbetaE hr.le
      have heq : beta * r⁻¹ * r = beta := by field_simp
      rw [heq] at hh
      simpa only [mul_comm] using hh
    have hu : r ≤ hi := free_ramp_annulus_modulus_le_of_energy_bound
      P t gamma0 hgamma0 hperiod0 hramp0 sigma0 B hB hr hBI hbelow.le
    refine ⟨r, ⟨hl, hu⟩, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, ?_⟩
    exact hE.trans_le (add_le_add le_rfl (min_le_left eps 1))
  obtain ⟨r, hr, -⟩ := hchoose 1 zero_lt_one
  exact ⟨lo, hi, hlo, hr.1.trans hr.2, hchoose⟩

end PoincareConjecture.M64
