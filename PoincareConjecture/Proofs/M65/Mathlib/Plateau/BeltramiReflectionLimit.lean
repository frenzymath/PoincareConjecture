import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiHolomorphic
import Mathlib.Analysis.Calculus.Deriv.Slope











set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff ComplexConjugate

namespace Complex





theorem fderiv_beltramiCircleReflect_tendsto (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hf : AnalyticAt ℂ (f : ℂ → ℂ) 0) (hd : deriv (f : ℂ → ℂ) 0 ≠ 0) :
    Tendsto (fderiv ℝ (beltramiCircleReflect f)) (cocompact ℂ)
      (𝓝 ((conj (deriv (f : ℂ → ℂ) 0))⁻¹ • ContinuousLinearMap.id ℝ ℂ)) := by
  let c := deriv (f : ℂ → ℂ) 0
  let rho := fun z => conj (deriv (f : ℂ → ℂ) (beltramiCircleInversion z)) /
    (conj (f (beltramiCircleInversion z) / beltramiCircleInversion z)) ^ 2
  have hc : conj c ≠ 0 := star_ne_zero.mpr hd
  have hdc : ContinuousAt (deriv (f : ℂ → ℂ)) 0 :=
    ((hf.contDiffAt (n := 2)).derivWithin (m := 0) (by norm_num)).continuousAt
  have hJ := beltramiCircleInversion_tendsto_zero
  have hnum : Tendsto (fun z => conj (deriv (f : ℂ → ℂ) (beltramiCircleInversion z)))
      (cocompact ℂ) (𝓝 (conj c)) := by
    exact continuous_conj.continuousAt.tendsto.comp
      (hdc.tendsto.comp (hJ.mono_right nhdsWithin_le_nhds))
  have hslope : Tendsto (fun z => f z / z) (𝓝[≠] (0 : ℂ)) (𝓝 c) := by
    convert! hf.differentiableAt.hasDerivAt.tendsto_slope using 1
    funext z
    simp only [slope_def_field, hf0, sub_zero]
  have hden : Tendsto (fun z => conj (f (beltramiCircleInversion z) /
      beltramiCircleInversion z)) (cocompact ℂ) (𝓝 (conj c)) :=
    continuous_conj.continuousAt.tendsto.comp (hslope.comp hJ)
  have hrho : Tendsto rho (cocompact ℂ) (𝓝 ((conj c)⁻¹)) := by
    have hh := hnum.div (hden.pow 2) (pow_ne_zero 2 hc)
    have heq : conj c / (conj c) ^ 2 = (conj c)⁻¹ := by field_simp
    simpa only [heq, Pi.div_apply] using! hh
  have hnear : ∀ᶠ z in cocompact ℂ,
      DifferentiableAt ℂ (f : ℂ → ℂ) (beltramiCircleInversion z) :=
    (hJ.mono_right nhdsWithin_le_nhds).eventually
      (analyticAt_iff_eventually_differentiableAt.mp hf)
  have hneq : ∀ᶠ z in cocompact ℂ, z ≠ 0 :=
    (isCompact_singleton (x := (0 : ℂ))).compl_mem_cocompact
  have hactual : ∀ᶠ z in cocompact ℂ,
      fderiv ℝ (beltramiCircleReflect f) z = rho z • ContinuousLinearMap.id ℝ ℂ := by
    filter_upwards [hnear, hneq] with z hz hzne
    have hfn : f (beltramiCircleInversion z) ≠ 0 := by
      intro hh
      exact hzne ((beltramiCircleInversion_eq_zero z).mp (f.injective (hh.trans hf0.symm)))
    have hderiv := hasDerivAt_beltramiCircleReflect f hzne hz hfn
    rw [(hderiv.hasFDerivAt.restrictScalars ℝ).fderiv]
    ext v
    change v * (conj (deriv (f : ℂ → ℂ) (beltramiCircleInversion z)) /
        (z ^ 2 * conj (f (beltramiCircleInversion z)) ^ 2)) = rho z * v
    have halgebra : (conj (f (beltramiCircleInversion z) / beltramiCircleInversion z)) ^ 2 =
        z ^ 2 * conj (f (beltramiCircleInversion z)) ^ 2 := by
      simp only [beltramiCircleInversion, div_inv_eq_mul, map_mul, conj_conj, mul_pow]
      ring
    dsimp only [rho]
    rw [halgebra]
    ring
  exact (hrho.smul_const (ContinuousLinearMap.id ℝ ℂ)).congr'
    (hactual.mono fun _ h => h.symm)

end Complex
