import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiL2
import PoincareConjecture.Proofs.M65.Mathlib.Plateau.FourierPotential












set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform Filter
open scoped Topology SchwartzMap ContDiff ComplexConjugate

namespace MeasureTheory.Lp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]





theorem fourierInv_coe_ae_of_integrable (u : Lp ℂ 2 (volume : Measure E))
    (hu : Integrable (u : E → ℂ)) :
    (𝓕⁻ u : Lp ℂ 2 (volume : Measure E)) =ᵐ[volume] 𝓕⁻ (u : E → ℂ) := by
  have hc : Continuous (𝓕⁻ (u : E → ℂ)) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
      (by change Continuous (fun p : E × E => -inner ℝ p.1 p.2); fun_prop) hu
  apply ae_eq_of_integral_contDiff_smul_eq (μ := (volume : Measure E))
    ((Lp.memLp (𝓕⁻ u)).locallyIntegrable (by norm_num)) hc.locallyIntegrable
  intro g hg hs
  have hs' : HasCompactSupport (Complex.ofRealCLM ∘ g) := hs.comp_left rfl
  let G : 𝓢(E, ℂ) := hs'.toSchwartzMap
    (Complex.ofRealCLM.contDiff.comp hg)
  have htd := congrArg (fun T : 𝓢'(E, ℂ) => T G)
    (fourierInv_toTemperedDistribution_eq u)
  simp only [TemperedDistribution.fourierInv_apply, toTemperedDistribution_apply] at htd
  have hflip : (-innerₗ E).flip = -innerₗ E := by
    ext x y
    change -inner ℝ y x = -inner ℝ x y
    rw [real_inner_comm]
  have hF := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -innerₗ E) (f := (G : E → ℂ)) (g := (u : E → ℂ))
    (μ := (volume : Measure E)) (ν := (volume : Measure E))
    Real.continuous_fourierChar
    (by change Continuous (fun p : E × E => -inner ℝ p.1 p.2); fun_prop) G.integrable hu
  rw [hflip] at hF
  have hinv : ((𝓕⁻ G : 𝓢(E, ℂ)) : E → ℂ) = 𝓕⁻ (G : E → ℂ) :=
    SchwartzMap.fourierInv_coe G
  simp only [hinv] at htd
  convert! htd.symm.trans hF using 1

end MeasureTheory.Lp

namespace Complex




theorem beurlingL2_schwartz_ae (h : 𝓢(ℂ, ℂ)) :
    beurlingL2 (h.toLp 2 volume) =ᵐ[volume]
      𝓕⁻ (fun ξ => (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ) := by
  let u := 𝓕 (beurlingL2 (h.toLp 2 volume))
  have hu : u =ᵐ[volume] fun ξ => (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ := by
    have hB := fourier_beurlingL2_ae (h.toLp 2 volume)
    rw [SchwartzMap.toLp_fourier_eq] at hB
    filter_upwards [hB, (𝓕 h).coeFn_toLp 2 volume] with ξ hξ hFξ
    exact hξ.trans (congrArg (fun v => (conj ξ / ξ) * v) hFξ)
  have hm : Integrable (fun ξ => (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ) := by
    have hmeas : Measurable (fun ξ => (conj ξ / ξ) * (𝓕 h : 𝓢(ℂ, ℂ)) ξ) := by
      fun_prop
    apply ((𝓕 h).integrable (μ := (volume : Measure ℂ))).norm.mono'
      hmeas.aestronglyMeasurable
    filter_upwards with ξ
    rw [norm_mul, norm_div, norm_conj]
    by_cases hξ : ξ = 0
    · simp [hξ]
    · simp [norm_ne_zero_iff.mpr hξ]
  have huint : Integrable (u : ℂ → ℂ) := hm.congr hu.symm
  have hinv := Lp.fourierInv_coe_ae_of_integrable u huint
  have hreps : (𝓕⁻ u : Lp ℂ 2 (volume : Measure ℂ)) = beurlingL2 (h.toLp 2 volume) :=
    fourierInv_fourier_eq _
  rw [hreps] at hinv
  exact hinv.trans (Eventually.of_forall (Real.fourierInv_congr_ae hu))






theorem dz_schwartzDbarPotential_beurlingL2_ae (h : 𝓢(ℂ, ℂ)) :
    (fun z => (fderiv ℝ (schwartzDbarPotential h) z 1 -
      I * fderiv ℝ (schwartzDbarPotential h) z I) / 2) =ᵐ[volume]
        beurlingL2 (h.toLp 2 volume) := by
  filter_upwards [beurlingL2_schwartz_ae h] with z hz
  exact (dz_schwartzDbarPotential h z).trans hz.symm

end Complex
