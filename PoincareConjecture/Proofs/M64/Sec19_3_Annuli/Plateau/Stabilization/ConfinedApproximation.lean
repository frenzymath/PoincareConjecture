import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.RetainedWinding
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeModulusConfinedApproximation












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Topology Manifold ContDiff Bundle

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}

local notation "Strip" => preimage (fun p : LoopPlane => p 1) (Ioo (0 : ℝ) 1)




theorem auxiliaryCircle_free_approximation_confined
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp : M63IsRampAt P gamma0 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
    let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
    ∃ lo hi : ℝ, 0 < lo ∧ lo ≤ hi ∧ ∀ eps : ℝ, 0 < eps →
      ∃ r : ℝ, r ∈ Icc lo hi ∧
      ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
        (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
        ∃ B : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
          ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 B.map Strip ∧
          IntegrableOn (fun p => (r * m60AreaGram (Q.flow.metric time) B.map p 0 0 +
            r⁻¹ * m60AreaGram (Q.flow.metric time) B.map p 1 1) / 2) m64AnnulusDomain ∧
          m64ClassicalWeightedGramEnergy (Q.flow.metric time) B r <
            m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + eps := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  have hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c0 :=
    ((auxiliaryCircle_section_contMDiff Q _).of_le (by simp)).comp
      (hgamma0.of_le (by norm_num))
  have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c1 :=
    ((auxiliaryCircle_section_contMDiff Q _).of_le (by simp)).comp
      (hgamma1.of_le (by norm_num))
  have hperiod0 : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient 0)) (hp0 x)
  have hperiod1 : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient delta)) (hp1 x)
  have hdisjoint : Disjoint (range c0) (range c1) :=
    auxiliaryCircle_separated_boundary_ranges Q gamma0 gamma1 hdelta hsmall
  obtain ⟨seed, -⟩ := auxiliaryCircle_radial_annulus Q time A0 delta
  obtain ⟨beta, hbeta, hlower⟩ := free_annulus_inverse_modulus_bound_of_disjoint_images
    (Q.flow.metric time) hc0 hc1 hperiod0 hperiod1 hdisjoint
  let level := m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + 1
  have hlevel : 0 < level := by
    dsimp only [level]
    linarith [m64LeastAnnulusArea_nonneg seed]
  let lo := beta / level
  let hi := (2 * curvePeriod * level) / circumference ^ 2
  have hlo : 0 < lo := div_pos hbeta hlevel
  have hcand (eps : ℝ) (heps : 0 < eps) :
      ∃ r : ℝ, r ∈ Icc lo hi ∧
      ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        StrictMono sigma0.map ∧ StrictMono sigma1.map ∧
        (∀ x : ℝ, 0 < deriv sigma0.map x) ∧ (∀ x : ℝ, 0 < deriv sigma1.map x) ∧
        ∃ B : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
          ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 B.map Strip ∧
          IntegrableOn (fun p => (r * m60AreaGram (Q.flow.metric time) B.map p 0 0 +
            r⁻¹ * m60AreaGram (Q.flow.metric time) B.map p 1 1) / 2) m64AnnulusDomain ∧
          m64ClassicalWeightedGramEnergy (Q.flow.metric time) B r <
            m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + eps := by
    have herr : 0 < min eps 1 := lt_min heps zero_lt_one
    obtain ⟨A, hA⟩ := m64LeastAnnulusArea_near_minimizer seed (half_pos herr)
    obtain ⟨r, hr, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, hBE⟩ :=
      M64Uniformization.exists_free_annulus_energy_lt_area A hc0 hc1 (half_pos herr)
    have hE : m64ClassicalWeightedGramEnergy (Q.flow.metric time) B r <
        m64LeastAnnulusArea (Q.flow.metric time) c0 c1 + min eps 1 := by linarith
    have hbelow : m64ClassicalWeightedGramEnergy (Q.flow.metric time) B r < level :=
      hE.trans_le (add_le_add le_rfl (min_le_right eps 1))
    have hl : lo ≤ r := by
      apply (div_le_iff₀ hlevel).mpr
      have hbetaE := (hlower sigma0 sigma1 hs0 hs1 B r hr).trans hbelow.le
      have hh := mul_le_mul_of_nonneg_right hbetaE hr.le
      have heq : beta * r⁻¹ * r = beta := by field_simp
      rw [heq] at hh
      simpa only [mul_comm] using hh
    have hu : r ≤ hi := auxiliaryCircle_free_annulus_modulus_le_original_winding
      P Q time gamma0 hgamma0 hp0 hramp (Q.circle.quotient 0) sigma0 B hB hr hbelow.le
    refine ⟨r, ⟨hl, hu⟩, sigma0, sigma1, hs0, hs1, hm0, hm1, hd0, hd1, B, hB, hBI, ?_⟩
    exact hE.trans_le (add_le_add le_rfl (min_le_left eps 1))
  obtain ⟨r, hr, -⟩ := hcand 1 zero_lt_one
  exact ⟨lo, hi, hlo, hr.1.trans hr.2, hcand⟩

end PoincareConjecture.M64
