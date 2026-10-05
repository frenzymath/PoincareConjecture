import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Projective
import PoincareLib.Topology.Manifold.Orientation.ProjectivePlane.Cover.InvolutionQuotient

/-!
# The antipodal covering of the frozen projective-plane thickening

The quotient map here is the actual `realProjectiveTwoSetoid` quotient from
the contract. Its product with the interval is a local homeomorphism and
identifies the antipodal deck map. Source: Hatcher, Example 1.43, p. 74;
Morgan--Tian Theorem 0.3, footnote 2, printed p. xii.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace Poincare.Topology.Orientation.ProjectivePlane

open PoincareMT

/-- The interval in the frozen projective-plane neighborhood predicate. -/
abbrev NormalInterval := Set.Ioo (-1 : Real) 1

/-- The sphere antipode, with its actual subspace topology.
Source: Hatcher, Example 1.43, p. 74. -/
def sphereAntipodeHomeomorph : UnitTwoSphere ≃ₜ UnitTwoSphere :=
  Homeomorph.neg _

/-- The frozen antipodal quotient projection is a local homeomorphism.
Source: Hatcher, Example 1.43, p. 74. -/
theorem projectivePlaneProjection_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk realProjectiveTwoSetoid) := by
  apply involutionQuotient_isLocalHomeomorph realProjectiveTwoSetoid
    sphereAntipodeHomeomorph
  · exact neg_neg
  · exact ne_neg_of_mem_unit_sphere Real
  · intro x y
    rfl

/-- The product antipodal projection, with the normal coordinate fixed.
Source: Hatcher, Example 1.43, p. 74, and Section 3.3, Exercise 5, p. 257. -/
def projectivePlaneCover : C(UnitTwoSphere × NormalInterval,
    RealProjectiveTwo × NormalInterval) :=
  ⟨fun z => (Quotient.mk realProjectiveTwoSetoid z.1, z.2),
    (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd⟩

/-- The product quotient is a topological local homeomorphism.
Source: Hatcher, Example 1.43, p. 74. -/
theorem projectivePlaneCover_isLocalHomeomorph : IsLocalHomeomorph projectivePlaneCover := by
  intro z
  obtain ⟨e, he, hq⟩ := projectivePlaneProjection_isLocalHomeomorph z.1
  refine ⟨e.prod (OpenPartialHomeomorph.refl NormalInterval), ⟨he, trivial⟩, ?_⟩
  funext p
  exact Prod.ext (congrFun hq p.1) rfl

/-- The involution of the sphere product fixes the quotient projection.
Source: Hatcher, Example 1.43, p. 74. -/
theorem projectivePlaneCover_antipodal (x : UnitTwoSphere) (t : NormalInterval) :
    projectivePlaneCover (-x, t) = projectivePlaneCover (x, t) := by
  apply Prod.ext
  · exact Quotient.sound (Or.inr rfl)
  · rfl

end Poincare.Topology.Orientation.ProjectivePlane
