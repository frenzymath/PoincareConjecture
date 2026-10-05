import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Barycentric.AffineSubdivisionComposition
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polyhedra.FinitePolyhedralRefinement

/-!
# Finite piecewise-affine maps on polyhedra

Closed polyhedral domains carry finite triangulations on which the
map has continuous affine formulas. Composition and inversion use
the checked subdivision and image-complex constructions. See Hudson
1969, pp. 5, 12--19, Hamilton pp. 64, 66--68 and M76 derivation 119.
-/

set_option autoImplicit false

open Set

namespace Geometry

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- A finite triangulation of the exact domain supports affine
formulas for the map. Values outside the domain are immaterial.
See Hudson pp. 5, 15--19 and M76 derivation 119. -/
def FinitePiecewiseAffineOn (f : E → F) (s : Set E) : Prop :=
  ∃ K : SimplicialComplex ℝ E, K.faces.Finite ∧ K.space = s ∧ K.AffineOnFaces f

variable {f f' : E → F} {g : F → G} {s : Set E} {t : Set F}

/-- A finite face-affine certificate gives the corresponding
domain property. See M76 derivation 119. -/
theorem SimplicialComplex.AffineOnFaces.finitePiecewiseAffineOn
    {K : SimplicialComplex ℝ E} (hf : K.AffineOnFaces f) (hK : K.faces.Finite) :
    FinitePiecewiseAffineOn f K.space := ⟨K, hK, rfl, hf⟩

/-- The finite PL property depends only on the values in its
stated domain. See Hudson p. 15 and M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.congr (hf : FinitePiecewiseAffineOn f s)
    (heq : EqOn f f' s) : FinitePiecewiseAffineOn f' s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨K, hK, rfl, hfaces.congr heq⟩

/-- A finite PL domain is compact. See Hudson p. 5 and
M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.isCompact (hf : FinitePiecewiseAffineOn f s) :
    IsCompact s := by
  obtain ⟨K, hK, rfl, _⟩ := hf
  exact K.isCompact_space_of_finite hK

/-- Finite piecewise-affine maps are continuous on their exact
domains. See Hudson pp. 15--17 and M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.continuousOn (hf : FinitePiecewiseAffineOn f s) :
    ContinuousOn f s := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact hfaces.continuousOn hK

/-- Finite PL maps compose after a finite source subdivision.
See Hudson pp. 15--17 and M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.comp [FiniteDimensional ℝ F]
    (hg : FinitePiecewiseAffineOn g t) (hf : FinitePiecewiseAffineOn f s)
    (hmap : MapsTo f s t) : FinitePiecewiseAffineOn (g ∘ f) s := by
  classical
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  obtain ⟨L, hL, rfl, hgfaces⟩ := hg
  let N := hK.toFinset.sup Finset.card
  have hN (r : Finset E) (hr : r ∈ K.faces) : r.card ≤ N + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hr)).trans (Nat.le_succ N)
  obtain ⟨R, hR, hRK, _, hcomp⟩ :=
    hfaces.exists_subdivision_comp hgfaces hK hL hmap hN
  exact ⟨R, hR, hRK.space_eq, hcomp⟩

/-- Restricting to a finite polyhedron preserves finite PL
regularity after refinement. See Hudson pp. 12--17 and
M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.restrict [FiniteDimensional ℝ E]
    (hf : FinitePiecewiseAffineOn f s) (J : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hJs : J.space ⊆ s) :
    FinitePiecewiseAffineOn f J.space := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  obtain ⟨R, hR, hRJ, href⟩ :=
    J.exists_finite_refinement_of_space_subset K hJ hK hJs
  exact ⟨R, hR, hRJ.space_eq, hfaces.of_face_containment href⟩

/-- Every carrier left inverse of an injective finite PL map
is finite PL on the exact image. See Hudson pp. 15--19 and
M76 derivation 119. -/
theorem FinitePiecewiseAffineOn.inverse [FiniteDimensional ℝ E]
    [FiniteDimensional ℝ F] (hf : FinitePiecewiseAffineOn f s)
    {g : F → E} (hleft : LeftInvOn g f s) :
    FinitePiecewiseAffineOn g (f '' s) := by
  obtain ⟨K, hK, rfl, hfaces⟩ := hf
  exact ⟨hfaces.embeddedImage hleft.injOn,
    hfaces.embeddedImage_finite _ hK, hfaces.embeddedImage_space _,
    hfaces.inverse_on_embeddedImage hleft.injOn hleft⟩

end Geometry
