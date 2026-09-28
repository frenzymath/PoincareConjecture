import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Positivity.Reaction
import Mathlib.Analysis.InnerProductSpace.PiL2








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped BigOperators

namespace Poincare.RicciFlow.Harnack

variable {I : Type*} [Fintype I]



theorem hamiltonBlock_posSemidef_of_unit_skew_quadratic_nonneg
    (R : I → I → I → I → ℝ) (P : I → I → I → ℝ) (M : I → I → ℝ)
    (hR : ∀ a b c d, R a b c d = R c d a b)
    (hfirst : ∀ a b c d, R a b c d = -R b a c d)
    (hlast : ∀ a b c d, R a b c d = -R a b d c)
    (hP : ∀ a b c, P a b c = -P b a c)
    (hM : ∀ a b, M a b = M b a)
    (hQ : ∀ z : EuclideanSpace ℝ ((I × I) ⊕ I), ‖z‖ = 1 →
      (∀ a b, z (Sum.inl (a, b)) = -z (Sum.inl (b, a))) →
      0 ≤ (∑ a, ∑ b, M a b * z (Sum.inr a) * z (Sum.inr b)) +
        2 * (∑ a, ∑ b, ∑ c,
          P a b c * z (Sum.inl (a, b)) * z (Sum.inr c)) +
        (∑ a, ∑ b, ∑ c, ∑ d,
          R a b c d * z (Sum.inl (a, b)) * z (Sum.inl (c, d)))) :
    (Matrix.fromBlocks
      (fun ac bd : I × I => R ac.1 ac.2 bd.1 bd.2)
      (fun (ac : I × I) d => P ac.1 ac.2 d)
      (fun c (bd : I × I) => P bd.1 bd.2 c) M).PosSemidef := by
  apply hamiltonBlock_posSemidef_of_skew_quadratic_nonneg R P M hR hfirst hlast hP hM
  intro U W hU
  let z : EuclideanSpace ℝ ((I × I) ⊕ I) :=
    WithLp.toLp 2 (Sum.elim (fun ab => U ab.1 ab.2) W)
  by_cases hz : z = 0
  · have hu (a b) : U a b = 0 := congrArg (fun z : EuclideanSpace ℝ ((I × I) ⊕ I) =>
      z (Sum.inl (a, b))) hz
    have hw (a) : W a = 0 := congrArg (fun z : EuclideanSpace ℝ ((I × I) ⊕ I) =>
      z (Sum.inr a)) hz
    simp only [hu, hw, mul_zero, Finset.sum_const_zero, add_zero, le_refl]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    let v : EuclideanSpace ℝ ((I × I) ⊕ I) := ‖z‖⁻¹ • z
    have hv : ‖v‖ = 1 := by
      simp only [v, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    have hskew (a b) : v (Sum.inl (a, b)) = -v (Sum.inl (b, a)) := by
      change ‖z‖⁻¹ * U a b = -(‖z‖⁻¹ * U b a)
      rw [hU a b, mul_neg]
    have h := hQ v hv hskew
    change 0 ≤ (∑ a, ∑ b, M a b * (‖z‖⁻¹ * W a) * (‖z‖⁻¹ * W b)) +
      2 * (∑ a, ∑ b, ∑ c, P a b c * (‖z‖⁻¹ * U a b) * (‖z‖⁻¹ * W c)) +
      (∑ a, ∑ b, ∑ c, ∑ d,
        R a b c d * (‖z‖⁻¹ * U a b) * (‖z‖⁻¹ * U c d)) at h
    have hmul (a b c : ℝ) : a * (‖z‖⁻¹ * b) * (‖z‖⁻¹ * c) =
        ‖z‖⁻¹ ^ 2 * (a * b * c) := by ring
    simp only [hmul, ← Finset.mul_sum] at h
    have heq (a b c : ℝ) :
        ‖z‖⁻¹ ^ 2 * a + 2 * (‖z‖⁻¹ ^ 2 * b) + ‖z‖⁻¹ ^ 2 * c =
          ‖z‖⁻¹ ^ 2 * (a + 2 * b + c) := by ring
    rw [heq] at h
    exact (mul_nonneg_iff_of_pos_left (sq_pos_of_ne_zero (inv_ne_zero hn))).mp h

end Poincare.RicciFlow.Harnack
