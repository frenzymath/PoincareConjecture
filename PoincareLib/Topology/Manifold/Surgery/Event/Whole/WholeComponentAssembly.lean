import PoincareLib.Topology.Manifold.Surgery.Event.Projective.ProjectiveDoubleConnectedSum
import PoincareLib.Topology.Manifold.Surgery.Event.Whole.WholeComponentGeometry
import PoincareLib.Topology.Manifold.Surgery.Event.One.OneCapAssembly
import PoincareLib.Topology.Manifold.Surgery.Event.Assembly.AssemblyTransport
import PoincareLib.Topology.Manifold.Surgery.Event.Component.ComponentAssemblyRefinement

/-!
# Classified assemblies on actual whole components

The projective double contributes two literal positive projective spaceforms,
joined along its actual separating collar. The stored smooth component map
then transports that connected sum onto the original component. The other
canonical alternatives contribute one classified summand.
Source: Morgan--Tian Proposition 15.3, printed pp. 357-358.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M38

attribute [local instance] SmoothClosedComponentModel.model_topology
  SmoothClosedComponentModel.model_charted SmoothClosedComponentModel.model_manifold

/-- The certificate's existing smooth model, with separation and countability
transported from the literal ambient component. -/
noncomputable def closedComponentModelCarrier (A : GeneralizedSliceCarrier.{u})
    (x : A.carrier) {kind : ClosedComponentKind}
    (C : SmoothClosedComponentModel kind (connectedComponent x)) :
    GeneralizedSliceCarrier.{u} := by
  let e := (componentClosedModelDiffeomorph A x C).toHomeomorph
  letI : MeasurableSpace C.model := borel C.model
  exact {
    carrier := C.model
    topologicalSpace := inferInstance
    measurableSpace := inferInstance
    borelSpace := ⟨rfl⟩
    chartedSpace := inferInstance
    isManifold := inferInstance
    t2Space := e.t2Space
    t3Space := e.t3Space
    secondCountable := e.symm.secondCountableTopology }

/-- One actual connected-sum operation assembles the projective double from
two closed positive-curvature summands. -/
theorem exists_projectiveDouble_assembly
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    Nonempty (SmoothFiniteConnectedSumAssembly
      ![projectiveCarrier.{u}, projectiveCarrier.{u}] A) := by
  obtain ⟨S⟩ := exists_projectiveDouble_connectedSum A C
  have hnon : Nonempty projectiveCarrier.{u}.carrier :=
    ⟨S.first_ball.map 0⟩
  let U := oneCapDisjointUnion projectiveCarrier.{u} projectiveCarrier.{u} hnon hnon
  exact ⟨U.toAssembly.tail ⟨projectiveCarrier, projectiveCarrier, ⟨U⟩, ⟨S⟩⟩⟩

/-- The assembly lands on the actual certified ambient component, using
the certificate's literal smooth maps in the final transport. -/
theorem exists_projectiveComponent_assembly
    (A : GeneralizedSliceCarrier.{u}) (x : A.carrier)
    (C : ClosedComponentCertificate .realProjectiveThreeConnectedSum
      (connectedComponent x)) :
    Nonempty (SmoothFiniteConnectedSumAssembly
      ![projectiveCarrier.{u}, projectiveCarrier.{u}] (componentCarrier A x)) := by
  let Q := closedComponentModelCarrier A x C.smooth_model
  obtain ⟨S⟩ := exists_projectiveDouble_assembly Q
    (Classical.choice C.smooth_model.standard_smooth)
  exact exists_transportAssembly S (componentClosedModelDiffeomorph A x C.smooth_model).symm

/-- Every whole compact canonical component has a classified finite
connected-sum assembly onto that exact component, including the projective
double. No standard geometry or assembly is assumed for the component. -/
theorem whole_canonical_component_assembly
    (N : RepairedNeckCapTopologyTheory.{u}) (F : SurgeryFlowData.{u}) (t : ℝ)
    (x : (F.slice t).carrier) (hx : IsCompact (connectedComponent x))
    (hcontrol : ∀ y ∈ connectedComponent x,
      SurgeryCanonicalControl F t y F.parameters.epsilon F.parameters.C)
    (hepsilon : F.parameters.epsilon ≤ N.epsilon₀) :
    ∃ n : ℕ, ∃ D : Fin n → GeneralizedSliceCarrier.{u},
      (∀ j, IsCompact (univ : Set (D j).carrier)) ∧
      (∀ j, IsConnected (univ : Set (D j).carrier)) ∧
      (∀ j, Nonempty (SurgerySphereBundle (D j)) ∨
        Nonempty (SurgeryPositiveSpaceform (D j))) ∧
      Nonempty (SmoothFiniteConnectedSumAssembly D (componentCarrier (F.slice t) x)) := by
  have hcompact : IsCompact (univ : Set (componentCarrier (F.slice t) x).carrier) :=
    isCompact_univ_iff.mpr (isCompact_iff_compactSpace.mp hx)
  rcases whole_canonical_component_geometry N F t x hx hcontrol hepsilon with hb | hp | hd
  · exact ⟨1, fun _ => componentCarrier (F.slice t) x, fun _ => hcompact,
      fun _ => componentCarrier_connected _ _, fun _ => Or.inl hb,
      ⟨(singletonDisjointUnion (componentCarrier (F.slice t) x)).toAssembly⟩⟩
  · exact ⟨1, fun _ => componentCarrier (F.slice t) x, fun _ => hcompact,
      fun _ => componentCarrier_connected _ _, fun _ => Or.inr hp,
      ⟨(singletonDisjointUnion (componentCarrier (F.slice t) x)).toAssembly⟩⟩
  · refine ⟨2, ![projectiveCarrier, projectiveCarrier], ?_, ?_, ?_,
      exists_projectiveComponent_assembly (F.slice t) x (Classical.choice hd)⟩
    · intro j
      fin_cases j <;> exact projectiveSpaceform.compact
    · intro j
      fin_cases j <;> exact projectiveSpaceform.connected
    · intro j
      fin_cases j <;> exact Or.inr ⟨projectiveSpaceform⟩

end PoincareMT.M38
