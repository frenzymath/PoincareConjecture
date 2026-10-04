import Mathlib.Data.Set.Card

/-!

# Strict image count from unchanged finite source vertices

An actual projected collision of distinct lifted values makes
the lifted image of one fixed finite source set strictly larger.
Its complement count in that same source bound therefore
decreases. See Hatcher, Theorem 3.1, p. 45 and M76 derivation 270.
-/

set_option autoImplicit false

namespace Set

/-- A collision among actual lifted values of the same finite
source set strictly increases its image cardinality upstairs.
The original source cardinality bounds both images, so its
remaining count strictly decreases. See Hatcher Theorem 3.1,
p. 45 and M76 derivation 270. -/
theorem ncard_image_lt_of_fixed_source_lift_collision
    {A E X : Type*} {s : Set A} (hs : s.Finite)
    {p : E → X} {f : A → X} {g : A → E}
    (hproj : ∀ a ∈ s, p (g a) = f a)
    {a b : A} (ha : a ∈ s) (hb : b ∈ s) (hne : g a ≠ g b) (heq : f a = f b) :
    (f '' s).ncard < (g '' s).ncard ∧ (g '' s).ncard ≤ s.ncard ∧
      s.ncard - (g '' s).ncard < s.ncard - (f '' s).ncard := by
  have himage : p '' (g '' s) = f '' s := by
    ext x
    constructor
    · rintro ⟨y, ⟨u, hu, rfl⟩, rfl⟩
      exact ⟨u, hu, (hproj u hu).symm⟩
    · rintro ⟨u, hu, rfl⟩
      exact ⟨g u, ⟨u, hu, rfl⟩, hproj u hu⟩
  have hle : (f '' s).ncard ≤ (g '' s).ncard := by
    rw [← himage]
    exact ncard_image_le (hs.image g)
  have hnecard : (f '' s).ncard ≠ (g '' s).ncard := by
    intro h
    have hcard : (p '' (g '' s)).ncard = (g '' s).ncard := by rw [himage, h]
    have hinj : InjOn p (g '' s) := injOn_of_ncard_image_eq hcard (hs.image g)
    exact hne (hinj ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      ((hproj a ha).trans (heq.trans (hproj b hb).symm)))
  have hlt : (f '' s).ncard < (g '' s).ncard := lt_of_le_of_ne hle hnecard
  have hbound : (g '' s).ncard ≤ s.ncard := ncard_image_le hs
  refine ⟨hlt, hbound, ?_⟩
  omega

end Set
