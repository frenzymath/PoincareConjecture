import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

set_option autoImplicit false

open Set
open scoped NNReal

namespace ApproximatesLinearOn

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {f : E → F} {Q : E →L[𝕜] F} {S : Set E} {T : Set F} {c K : ℝ≥0}

theorem comp_inverse_projection (hf : ApproximatesLinearOn f Q S c)
    (g : F → E) (hgS : MapsTo g T S) (hQg : ∀ u ∈ T, Q (g u) = u)
    (hg : ∀ u ∈ T, ∀ v ∈ T, ‖g u - g v‖ ≤ K * ‖u - v‖) :
    ApproximatesLinearOn (f ∘ g) (ContinuousLinearMap.id 𝕜 F) T (c * K) := by
  intro u hu v hv
  have h := hf (g u) (hgS hu) (g v) (hgS hv)
  rw [map_sub, hQg u hu, hQg v hv] at h
  change ‖f (g u) - f (g v) - (u - v)‖ ≤ (c * K : ℝ≥0) * ‖u - v‖
  calc
    _ ≤ c * ‖g u - g v‖ := h
    _ ≤ c * (K * ‖u - v‖) := mul_le_mul_of_nonneg_left (hg u hu v hv) c.coe_nonneg
    _ = _ := by rw [NNReal.coe_mul, mul_assoc]

theorem open_image_comp_inverse_projection [CompleteSpace F]
    (hf : ApproximatesLinearOn f Q S c)
    (g : F → E) (hgS : MapsTo g T S) (hQg : ∀ u ∈ T, Q (g u) = u)
    (hg : ∀ u ∈ T, ∀ v ∈ T, ‖g u - g v‖ ≤ K * ‖u - v‖)
    (hT : IsOpen T) (hsmall : c * K < 1) : IsOpen ((f ∘ g) '' T) := by
  rcases subsingleton_or_nontrivial F with h | h
  · exact isOpen_discrete _
  · have ha := hf.comp_inverse_projection g hgS hQg hg
    let e := ContinuousLinearEquiv.refl 𝕜 F
    have hbound : c * K < ‖(e.symm : F →L[𝕜] F)‖₊⁻¹ := by
      simpa [e] using hsmall
    exact (ha.toOpenPartialHomeomorph (f' := e) (f ∘ g) T (Or.inr hbound) hT).open_target

theorem injOn_of_inverse_secant_bound (hf : ApproximatesLinearOn f Q S c)
    (hQ : ∀ x ∈ S, ∀ y ∈ S, ‖x - y‖ ≤ K * ‖Q x - Q y‖)
    (hsmall : c * K < 1) : InjOn f S := by
  intro x hx y hy he
  have herr := hf x hx y hy
  rw [he, sub_self, zero_sub, norm_neg, map_sub] at herr
  have hbound := (hQ x hx y hy).trans (mul_le_mul_of_nonneg_left herr K.coe_nonneg)
  have hprod : (K : ℝ) * c < 1 := by
    exact_mod_cast (mul_comm c K ▸ hsmall)
  have hnonpos : (1 - (K : ℝ) * c) * ‖x - y‖ ≤ 0 := by nlinarith only [hbound]
  have hn : ‖x - y‖ ≤ 0 := nonpos_of_mul_nonpos_right hnonpos (sub_pos.mpr hprod)
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm hn (norm_nonneg _)))

end ApproximatesLinearOn
