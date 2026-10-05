import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Image

/-!
# Fixed levels of height-raising maps

Fixation of the original negative part and nondecreasing
height preserve every negative level. Fixation of an entire
target set and injectivity preserve its intersections with
all image carriers. See Alexander 1924, pp. 7--8 and M76
derivation 242.
-/

set_option autoImplicit false

open Set

/-- An injective map fixing an entire set preserves that set's
intersection with every image carrier. See Alexander pp. 7--8
and derivation 242. -/
theorem Function.Injective.image_inter_eq_of_fixed {E : Type*} {f : E → E}
    (hf : Function.Injective f) {s t : Set E} (hfix : ∀ x ∈ t, f x = x) :
    (f '' s) ∩ t = s ∩ t := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, hxy⟩, hyt⟩
    have heq : x = y := hf (hxy.trans (hfix y hyt).symm)
    exact ⟨heq ▸ hx, hyt⟩
  · intro hy
    exact ⟨⟨y, hy.1, hfix y hy.2⟩, hy.2⟩

namespace Set

/-- A map never lowering height and fixing the original
negative part preserves every negative level of its carrier.
See Alexander pp. 7--8 and derivation 242. -/
theorem image_negative_level_eq_of_height_le {E : Type*} {S : Set E} (A : E → ℝ)
    (f : E → E) (hraise : ∀ x ∈ S, A x ≤ A (f x))
    (hfix : ∀ x ∈ S, A x < 0 → f x = x) {c : ℝ} (hc : c < 0) :
    (f '' S) ∩ {x | A x = c} = S ∩ {x | A x = c} := by
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hxA⟩
    have hxneg : A x < 0 := (hraise x hx).trans_lt (hxA ▸ hc)
    exact ⟨(hfix x hx hxneg).symm ▸ hx, hxA⟩
  · intro hy
    exact ⟨⟨y, hy.1, hfix y hy.1 (hy.2 ▸ hc)⟩, hy.2⟩

end Set
