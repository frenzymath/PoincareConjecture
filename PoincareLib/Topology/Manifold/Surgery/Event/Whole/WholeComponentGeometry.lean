import PoincareLib.Topology.Manifold.Surgery.Event.Whole.WholeComponentModels
import PoincareLib.Topology.Manifold.Surgery.Event.Round.RoundComponentSpaceforms
import PoincareLib.Topology.Manifold.Surgery.Event.Sphere.SphereBundles

/-!
# Geometry of whole disappearing components

The actual closed sphere, projective, round, and sphere-bundle models give
the corresponding geometric summands on their literal components. The
projective double is retained as its exact certificate for the subsequent
two-summand assembly. No proper discarded subregion is classified here.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.M38

/-- Whole compact canonical components are actual sphere-bundle or
positive-spaceform summands, or have the exact supplied projective-double
certificate. Source: Proposition 15.3, pp. 357-358, whole components. -/
theorem whole_canonical_component_geometry
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u}) (t : ℝ)
    (x : (F.slice t).carrier) (hx : IsCompact (connectedComponent x))
    (hcontrol : ∀ y ∈ connectedComponent x,
      SurgeryCanonicalControl F t y F.parameters.epsilon F.parameters.C)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    Nonempty (SurgerySphereBundle (componentCarrier (F.slice t) x)) ∨
    Nonempty (SurgeryPositiveSpaceform (componentCarrier (F.slice t) x)) ∨
    Nonempty (ClosedComponentCertificate .realProjectiveThreeConnectedSum
      (connectedComponent x)) := by
  rcases whole_canonical_component_models N F t x hx hcontrol hepsilon with
    ⟨kind, ⟨C⟩⟩ | ⟨Q, hQ⟩ | ⟨Q, hQ⟩
  · cases kind with
    | threeSphere =>
      exact Or.inr (Or.inl ⟨sphereSpaceformOnComponent (F.slice t) x C⟩)
    | realProjectiveThree =>
      exact Or.inr (Or.inl ⟨projectiveSpaceformOnComponent (F.slice t) x C⟩)
    | realProjectiveThreeConnectedSum =>
      exact Or.inr (Or.inr ⟨C⟩)
  · exact Or.inl ⟨bundleOnComponent (F.slice t) Q x hQ⟩
  · exact Or.inr (Or.inl ⟨roundSpaceformOnComponent (F.slice t) Q x hQ⟩)

end PoincareMT.M38
