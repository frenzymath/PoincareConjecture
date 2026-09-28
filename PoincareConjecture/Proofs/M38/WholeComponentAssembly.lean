import PoincareConjecture.Proofs.M38.ProjectiveDoubleConnectedSum
import PoincareConjecture.Proofs.M38.WholeComponentGeometry
import PoincareConjecture.Proofs.M38.OneCapAssembly
import PoincareConjecture.Proofs.M38.AssemblyTransport
import PoincareConjecture.Proofs.M38.ComponentAssemblyRefinement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M38

attribute [local instance] SmoothClosedComponentModel.model_topology
  SmoothClosedComponentModel.model_charted SmoothClosedComponentModel.model_manifold

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

theorem exists_projectiveDouble_assembly
    (A : GeneralizedSliceCarrier.{u}) (C : SmoothProjectiveDoubleModel A.carrier) :
    Nonempty (SmoothFiniteConnectedSumAssembly
      ![projectiveCarrier.{u}, projectiveCarrier.{u}] A) := by
  obtain ⟨S⟩ := exists_projectiveDouble_connectedSum A C
  have hnon : Nonempty projectiveCarrier.{u}.carrier :=
    ⟨S.first_ball.map 0⟩
  let U := oneCapDisjointUnion projectiveCarrier.{u} projectiveCarrier.{u} hnon hnon
  exact ⟨U.toAssembly.tail ⟨projectiveCarrier, projectiveCarrier, ⟨U⟩, ⟨S⟩⟩⟩

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

end PoincareConjecture.M38
