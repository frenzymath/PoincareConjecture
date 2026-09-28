import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.Stabilization.FreeRampClassicalMinimum
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.AnnulusAffinePhase
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.FinitePhaseImmersion
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Boundary.RelabelAreaRange






noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [CompactSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Icc a b)} {circumference auxiliary : ℝ}





theorem auxiliaryCircle_free_ramp_immersed_minimum
    (P : M62.CircleProductData F circumference)
    (Q : M62.CircleProductData P.flow auxiliary) (time : ℝ)
    (gamma0 gamma1 : ℝ → P.charts.Point)
    (hgamma0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma0)
    (hgamma1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 (n + 1)) 2 gamma1)
    (hp0 : Function.Periodic gamma0 curvePeriod)
    (hp1 : Function.Periodic gamma1 curvePeriod)
    (hramp0 : M63IsRampAt P gamma0 time) (hramp1 : M63IsRampAt P gamma1 time)
    (A0 : M64Annulus (P.flow.metric time) gamma0 gamma1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta < auxiliary) :
    let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
    let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
    ∃ r : ℝ, 0 < r ∧ ∃ sigma0 sigma1 : M64PeriodicDegreeOneLift,
      ∃ A : M64Annulus (Q.flow.metric time) (c0 ∘ sigma0.map) (c1 ∘ sigma1.map),
        ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) 1 A.map
          {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} ∧
        ContMDiffOn (𝓡 2) (𝓡 ((n + 1) + 1)) ∞ A.map m64AnnulusOpenStrip ∧
        ContDiff ℝ 1 sigma0.map ∧ ContDiff ℝ 1 sigma1.map ∧
        A.area = m64LeastAnnulusArea (Q.flow.metric time) c0 c1 ∧
        (∀ᵐ p ∂volume.restrict m64AnnulusDomain,
          r * m60AreaGram (Q.flow.metric time) A.map p 0 0 =
            r⁻¹ * m60AreaGram (Q.flow.metric time) A.map p 1 1 ∧
          m60AreaGram (Q.flow.metric time) A.map p 0 1 = 0) ∧
        (∃ c : ℝ, c ≠ 0 ∧ Q.circle.quotient c = Q.circle.quotient delta ∧
          ∀ p, p 1 ∈ Icc (0 : ℝ) 1 → (A.map p).2 = Q.circle.quotient (c * p 1)) ∧
        ∀ p ∈ m64AnnulusDomain,
          0 < m64AnnulusWithinGram (Q.flow.metric time) A.map p 0 0 ∧
          0 < m64AnnulusWithinGram (Q.flow.metric time) A.map p 1 1 ∧
          Function.Injective
            (mfderivWithin (𝓡 2) (𝓡 ((n + 1) + 1)) A.map m64AnnulusDomain p) := by
  let : Fact (0 < circumference) := ⟨P.circle.positive⟩
  let : Fact (0 < auxiliary) := ⟨Q.circle.positive⟩
  let c0 := auxiliaryCircleSection Q (Q.circle.quotient 0) ∘ gamma0
  let c1 := auxiliaryCircleSection Q (Q.circle.quotient delta) ∘ gamma1
  obtain ⟨r, hr, sigma0, sigma1, A, hAc, hAi, hs0, hs1, hminimum, hconformal⟩ :=
    auxiliaryCircle_free_ramp_classical_minimum P Q time gamma0 gamma1 hgamma0 hgamma1
      hp0 hp1 hramp0 hramp1 A0 hdelta hsmall
  have hc0 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c0 :=
    ((auxiliaryCircle_section_contMDiff Q (Q.circle.quotient 0)).of_le (by simp)).comp
      (hgamma0.of_le (by norm_num))
  have hc1 : ContMDiff 𝓘(ℝ, ℝ) (𝓡 ((n + 1) + 1)) 1 c1 :=
    ((auxiliaryCircle_section_contMDiff Q (Q.circle.quotient delta)).of_le (by simp)).comp
      (hgamma1.of_le (by norm_num))
  have hper0 : Function.Periodic c0 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient 0)) (hp0 x)
  have hper1 : Function.Periodic c1 curvePeriod :=
    fun x => congrArg (auxiliaryCircleSection Q (Q.circle.quotient delta)) (hp1 x)
  have hmin : A.area = m64LeastAnnulusArea (Q.flow.metric time)
      (c0 ∘ sigma0.map) (c1 ∘ sigma1.map) := by
    rw [leastAnnulusArea_comp_lifts_of_C1 hc0 hper0 hc1 hper1 sigma0 sigma1]
    exact hminimum
  obtain ⟨c, hc, hcq, hphase⟩ := m64Annulus_exists_nonzero_affine_phase Q time A hr hmin
    hconformal hAc.continuousOn hAi (fun _ => rfl) hdelta hsmall (fun _ => rfl)
  have hsub : m64AnnulusInterior ⊆ m64AnnulusOpenStrip :=
    fun _ hp => hp 1 (mem_univ _)
  have hrect : m64AnnulusDomain ⊆ {p : LoopPlane | p 1 ∈ Icc (0 : ℝ) 1} :=
    fun _ hp => ⟨hp.2.2.1, hp.2.2.2⟩
  exact ⟨r, hr, sigma0, sigma1, A, hAc, hAi, hs0, hs1, hminimum, hconformal,
    ⟨c, hc, hcq, hphase⟩, m64Annulus_affine_phase_within_immersion Q time A hr
      (hAc.mono hrect) (hAi.mono hsub) hconformal hc (fun p hp => hphase p (hrect hp))⟩

end PoincareConjecture.M64
