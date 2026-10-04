import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Maps.FinitePLHomeomorph
import Mathlib.Topology.Algebra.ContinuousAffineEquiv

/-!
# Affine coordinate changes for finite PL maps

Affine coordinate changes transport the exact finite domain
triangulation. This permits coning about arbitrary interior
points. See Hudson 1969, pp. 15--19 and M76 derivations 119--120.
-/

set_option autoImplicit false

open Set Geometry

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E}

/-- Affine postcomposition preserves finite PL formulas on
the same domain. See Hudson p. 15 and M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.postcomp (hf : FinitePiecewiseAffineOn f s)
    (a : F →ᴬ[ℝ] G) : FinitePiecewiseAffineOn (a ∘ f) s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨K, hK, rfl, hfaces.postcomp a⟩

/-- Affine changes of source coordinates transport the domain
triangulation and preserve finite PL regularity.
See Hudson pp. 15--19 and M76 derivation 120. -/
theorem FinitePiecewiseAffineOn.precomp_affineEquiv [FiniteDimensional ℝ E]
    (hf : FinitePiecewiseAffineOn f s) (a : G ≃ᴬ[ℝ] E) :
    FinitePiecewiseAffineOn (f ∘ a) (a.symm '' s) := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  have hA := K.affineOnFaces_affine a.symm.toContinuousAffineMap
  let L := hA.embeddedImage a.symm.injective.injOn
  have hL : L.space = a.symm '' K.space := hA.embeddedImage_space _
  have ha : FinitePiecewiseAffineOn a (a.symm '' K.space) :=
    ⟨L, hA.embeddedImage_finite _ hK, hL, L.affineOnFaces_affine a.toContinuousAffineMap⟩
  exact hfaces.finitePiecewiseAffineOn hK |>.comp ha (by
    rintro _ ⟨x, hx, rfl⟩
    simpa using hx)

end Geometry

namespace Homeomorph

/-- Affine changes of both ambient coordinates preserve finite
PL homeomorphisms, with the exact transported source and target.
See Hudson pp. 15--19 and M76 derivation 120. -/
theorem IsFinitePL.affine_conjugate {E F E' F' : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [NormedAddCommGroup F'] [NormedSpace ℝ F']
    {s : Set E} {t : Set F} {e : s ≃ₜ t} (he : e.IsFinitePL)
    (a : E ≃ᴬ[ℝ] E') (b : F ≃ᴬ[ℝ] F') :
    ((a.toHomeomorph.image s).symm.trans (e.trans (b.toHomeomorph.image t))).IsFinitePL := by
  obtain ⟨f, hf, he⟩ := he
  refine ⟨b ∘ (f ∘ a.symm), (hf.precomp_affineEquiv a.symm).postcomp b.toContinuousAffineMap, ?_⟩
  intro x
  change b (e ((a.toHomeomorph.image s).symm x)) = b (f (a.symm x))
  rw [he]
  rfl

end Homeomorph
