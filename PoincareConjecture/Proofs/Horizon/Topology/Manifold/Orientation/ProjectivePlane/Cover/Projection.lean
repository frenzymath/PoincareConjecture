import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Projective
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Orientation.ProjectivePlane.Cover.InvolutionQuotient









set_option autoImplicit false

noncomputable section

open Set
open scoped Topology

namespace Poincare.Topology.Orientation.ProjectivePlane

open PoincareConjecture


abbrev NormalInterval := Set.Ioo (-1 : Real) 1



def sphereAntipodeHomeomorph : UnitTwoSphere ≃ₜ UnitTwoSphere :=
  Homeomorph.neg _



theorem projectivePlaneProjection_isLocalHomeomorph :
    IsLocalHomeomorph (Quotient.mk realProjectiveTwoSetoid) := by
  apply involutionQuotient_isLocalHomeomorph realProjectiveTwoSetoid
    sphereAntipodeHomeomorph
  · exact neg_neg
  · exact ne_neg_of_mem_unit_sphere Real
  · intro x y
    rfl



def projectivePlaneCover : C(UnitTwoSphere × NormalInterval,
    RealProjectiveTwo × NormalInterval) :=
  ⟨fun z => (Quotient.mk realProjectiveTwoSetoid z.1, z.2),
    (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd⟩



theorem projectivePlaneCover_isLocalHomeomorph : IsLocalHomeomorph projectivePlaneCover := by
  intro z
  obtain ⟨e, he, hq⟩ := projectivePlaneProjection_isLocalHomeomorph z.1
  refine ⟨e.prod (OpenPartialHomeomorph.refl NormalInterval), ⟨he, trivial⟩, ?_⟩
  funext p
  exact Prod.ext (congrFun hq p.1) rfl



theorem projectivePlaneCover_antipodal (x : UnitTwoSphere) (t : NormalInterval) :
    projectivePlaneCover (-x, t) = projectivePlaneCover (x, t) := by
  apply Prod.ext
  · exact Quotient.sound (Or.inr rfl)
  · rfl

end Poincare.Topology.Orientation.ProjectivePlane
