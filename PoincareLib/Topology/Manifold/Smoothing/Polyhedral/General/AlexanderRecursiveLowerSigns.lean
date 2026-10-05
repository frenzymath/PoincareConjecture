import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderRecursiveRetainedSigns
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Levels.AlexanderRecursiveRimLevel

/-!
# Both ordinary child height signs up to and including the moved rim

The literal cap/remainder cover and pointwise retained-sign
transport include the exact rim height. Only the actual cap
birth point is omitted. See Alexander 1924, p. 7 and M76
derivation 256.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Original signs and actual nonbirth cap signs give both
height approaches at every positive child point up to the
rim height, using the same retained map throughout. See
Alexander p. 7 and M76 derivation 256. -/
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
