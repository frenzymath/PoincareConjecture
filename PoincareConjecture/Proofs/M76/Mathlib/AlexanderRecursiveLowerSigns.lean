import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRetainedSigns
import PoincareConjecture.Proofs.M76.Mathlib.AlexanderRecursiveRimLevel

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem AlexanderCollarSlab.ordinary_lower_band_mem_both_height_closures
    {S s s' d rim TX TY : Set E} {A : E →ᵃ[ℝ] ℝ} {q p : E} {β t : ℝ}
    (M : AlexanderCollarSlab S A q β)
    (hs' : IsClosed s') (hunion : s ∪ s' = S)
    (hcut : s ∩ s' ⊆ {x | A x = 0})
    (hsplit : M.collar ∩ s = TX ∪ TY) (hdisj : Disjoint TX TY)
    (hrim : IsClosed rim)
    (hY : ∀ w : {w : E × ℝ | w.1 ∈ S ∩ {x | A x = 0} ∧
        w.2 ∈ Icc 0 (M.upper w.1)},
      (M.chart w : E) ∈ TY ↔ (w : E × ℝ).1 ∈ rim)
    (H : E ≃ₜ E) (hraise : ∀ x ∈ s, A x ≤ A (H x))
    (hneg : ∀ x ∈ s, A x < 0 → H x = x)
    (hfix : ∀ x ∈ M.residual, H x = x)
    (ht : t < β) (hroof : ∀ x ∈ rim, t < M.upper x)
    (hmoved : ∀ x ∈ TY, t ≤ A (H x))
    (hrigidity : ∀ x ∈ TY, A (H x) = t → x ∈ d)
    (F : (TX ∪ (M.residual ∩ s) : Set E) ≃ₜ
      ((H '' TX) ∪ (M.residual ∩ s) : Set E))
    (hFA : ∀ x, A (F x) = A x)
    (hsource : ∀ x ∈ S, A x ∈ Ioc (0 : ℝ) t →
      x ∈ closure (S ∩ {y | A y < A x}) ∧
        x ∈ closure (S ∩ {y | A x < A y}))
    (hcap : ∀ x ∈ H '' d, x ≠ H p →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y})) :
    ∀ x ∈ H '' (s ∪ d), A x ∈ Ioc (0 : ℝ) t → x ≠ H p →
      x ∈ closure ((H '' (s ∪ d)) ∩ {y | A y < A x}) ∧
        x ∈ closure ((H '' (s ∪ d)) ∩ {y | A x < A y}) := by
  have hcover := M.ordinary_lower_band_eq_cap_union_remainder
    (subset_union_left.trans hunion.subset) hsplit H hraise hneg hfix ht.le hmoved hrigidity
  intro x hx hxA hxne
  rcases (hcover.subset ⟨hx, hxA⟩).1 with hxD | hxR
  · exact hcap x hxD hxne
  · exact M.ordinary_retained_mem_both_height_closures hs' hunion hcut
      hsplit hdisj hrim hY H hfix ht hroof F hFA hsource x hxR hxA

end Geometry
