import PoincareConjecture.Proofs.M65.Mathlib.Plateau.BeltramiReflectionLimit










set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology ContDiff ComplexConjugate

namespace Complex

private theorem inversion_hasFDerivAt {z : ℂ} (hz : z ≠ 0) :
    HasFDerivAt beltramiCircleInversion
      (-(beltramiCircleInversion z) ^ 2 • conjCLE.toContinuousLinearMap) z := by
  have hh := ((hasDerivAt_inv (star_ne_zero.mpr hz)).hasFDerivAt.restrictScalars ℝ).comp z
    conjCLE.hasFDerivAt
  convert! hh using 1
  ext v
  change -(beltramiCircleInversion z) ^ 2 * conj v = conj v * (-(conj z ^ 2)⁻¹)
  simp only [beltramiCircleInversion, inv_pow]
  ring

private theorem reflected_fderiv_apply (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hf : Differentiable ℝ (f : ℂ → ℂ)) {z : ℂ} (hz : z ≠ 0) (v : ℂ) :
    fderiv ℝ (beltramiCircleReflect f) z v =
      -(beltramiCircleInversion (f (beltramiCircleInversion z))) ^ 2 *
        conj (fderiv ℝ (f : ℂ → ℂ) (beltramiCircleInversion z)
          (-(beltramiCircleInversion z) ^ 2 * conj v)) := by
  have hne : f (beltramiCircleInversion z) ≠ 0 := by
    intro hh
    exact hz ((beltramiCircleInversion_eq_zero z).mp (f.injective (hh.trans hf0.symm)))
  have hd := (inversion_hasFDerivAt hne).comp z
    ((hf (beltramiCircleInversion z)).hasFDerivAt.comp z (inversion_hasFDerivAt hz))
  change fderiv ℝ (beltramiCircleInversion ∘ f ∘ beltramiCircleInversion) z v = _
  rw [hd.fderiv]
  rfl





theorem beltramiReflectedHomeomorph_equation (f : ℂ ≃ₜ ℂ) (hf0 : f 0 = 0)
    (hf : ContDiff ℝ ∞ (f : ℂ → ℂ)) (μ : ℂ → ℂ)
    (hμ : HasCompactSupport μ) (hμ0 : μ 0 = 0)
    (heq : ∀ z, fderiv ℝ (f : ℂ → ℂ) z 1 + I * fderiv ℝ (f : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (f : ℂ → ℂ) z 1 - I * fderiv ℝ (f : ℂ → ℂ) z I))
    (href : ∀ z ≠ 0, μ z = (z / conj z) ^ 2 * conj (μ (beltramiCircleInversion z))) :
    ∀ z, fderiv ℝ (beltramiReflectedHomeomorph f hf0 : ℂ → ℂ) z 1 +
        I * fderiv ℝ (beltramiReflectedHomeomorph f hf0 : ℂ → ℂ) z I =
      μ z * (fderiv ℝ (beltramiReflectedHomeomorph f hf0 : ℂ → ℂ) z 1 -
        I * fderiv ℝ (beltramiReflectedHomeomorph f hf0 : ℂ → ℂ) z I) := by
  intro z
  change fderiv ℝ (beltramiCircleReflect f) z 1 +
      I * fderiv ℝ (beltramiCircleReflect f) z I =
    μ z * (fderiv ℝ (beltramiCircleReflect f) z 1 -
      I * fderiv ℝ (beltramiCircleReflect f) z I)
  by_cases hz : z = 0
  · subst z
    have hh := analyticAt_beltramiCircleReflect_zero f hf0
      (eventually_holomorphic_of_compact_beltrami f μ
        (hf.differentiable (by simp)) hμ heq)
    rw [(hh.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv, hμ0]
    change 1 * deriv (beltramiCircleReflect f) 0 +
      I * (I * deriv (beltramiCircleReflect f) 0) = 0 * _
    simp only [one_mul, ← mul_assoc, I_mul_I, neg_one_mul, add_neg_cancel, zero_mul]
  · let u := beltramiCircleInversion z
    let A := -(beltramiCircleInversion (f u)) ^ 2
    let B := -u ^ 2
    let w := (fderiv ℝ (f : ℂ → ℂ) u 1 - I * fderiv ℝ (f : ℂ → ℂ) u I) / 2
    have hcoeff : conj B * μ z = conj (μ u) * B := by
      dsimp only [B, u]
      rw [href z hz]
      simp only [beltramiCircleInversion, map_neg, map_pow, map_inv₀, conj_conj]
      have hc : conj z ≠ 0 := star_ne_zero.mpr hz
      field_simp
    have hd (v : ℂ) : fderiv ℝ (beltramiCircleReflect f) z v =
        (A * conj w * conj B) * (v + μ z * conj v) := by
      rw [reflected_fderiv_apply f hf0 (hf.differentiable (by simp)) hz v]
      change A * conj (fderiv ℝ (f : ℂ → ℂ) u (B * conj v)) = _
      rw [linearMap_beltrami_formula _ (μ u) (heq u)]
      change A * conj (w * (B * conj v + μ u * conj (B * conj v))) = _
      simp only [map_mul, map_add, conj_conj]
      calc
        _ = (A * conj w * conj B) * v +
            (A * conj w) * (conj (μ u) * B) * conj v := by ring
        _ = _ := by rw [← hcoeff]; ring
    rw [hd 1, hd I]
    simp only [map_one, conj_I]
    ring_nf
    simp only [I_sq]
    ring

end Complex
