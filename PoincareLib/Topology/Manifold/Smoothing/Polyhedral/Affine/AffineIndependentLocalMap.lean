import Mathlib.LinearAlgebra.AffineSpace.Independent

/-!
# Affine independence under maps injective on the relevant span

Equality of image affine combinations pulls back whenever the map
is injective on their affine span. See Cairns 1940, pp. 804--806
and M76 derivation 70.
-/

set_option autoImplicit false

open Set Affine

namespace AffineIndependent

variable {ι 𝕜 E F P Q : Type*} [Ring 𝕜] [Nontrivial 𝕜]
  [AddCommGroup E] [Module 𝕜 E] [AffineSpace E P]
  [AddCommGroup F] [Module 𝕜 F] [AffineSpace F Q]

/-- Injectivity on the span of a family suffices to preserve
affine independence. See Cairns pp. 804--806 and M76 derivation 70. -/
theorem map_of_injOn_affineSpan {p : ι → P} (hp : AffineIndependent 𝕜 p)
    (f : P →ᵃ[𝕜] Q) (hf : InjOn f (affineSpan 𝕜 (range p))) :
    AffineIndependent 𝕜 (f ∘ p) := by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  intro s t w z hw hz he
  apply hp.indicator_eq_of_affineCombination_eq s t w z hw hz
  apply hf (affineCombination_mem_affineSpan hw p) (affineCombination_mem_affineSpan hz p)
  simpa only [Finset.map_affineCombination _ p w hw f,
    Finset.map_affineCombination _ p z hz f] using he

end AffineIndependent
