import PoincareConjecture.Proofs.M40.DegreeOfComparison
import PoincareConjecture.Proofs.M40.Mathlib.DegreeHomotopySphere














set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareConjecture.M40





theorem exists_homotopyEquiv_of_homotopy_three_spheres
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (eX : X ≃ₕ ThreeSphere) (eY : Y ≃ₕ ThreeSphere)
    (f : C(X, Y)) (hbij : Function.Bijective (surgeryThirdHomologyMap f)) :
    ∃ e : X ≃ₕ Y, e.toFun = f := by
  let S := ULift.{u} ThreeSphere
  let eS : S ≃ₜ ThreeSphere := Homeomorph.ulift
  let EX : X ≃ₕ S := eX.trans eS.symm.toHomotopyEquiv
  let EY : Y ≃ₕ S := eY.trans eS.symm.toHomotopyEquiv
  apply Proofs.M40.Topology.exists_homotopyEquiv_of_conjugate EX EY f
  apply Proofs.M40.Topology.exists_homotopyEquiv_threeSphere_of_homology_bijective
    eS (EY.toFun.comp (f.comp EX.invFun))
  exact Proofs.M40.Topology.homologyMap_bijective_conjugate EX EY f hbij

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonHomotopyInput D T hT}
  (Q : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput)




theorem comparison_homotopy_equivalence (P : RepairedClosedTopologyProvider.{u}) :
    ∃ e : I.parent.carrier.carrier ≃ₕ I.child.carrier.carrier, e.toFun = Q.map := by
  letI : CompactSpace I.parent.carrier.carrier :=
    isCompact_univ_iff.mp I.parent.compact
  letI : CompactSpace I.child.carrier.carrier :=
    isCompact_univ_iff.mp I.child.compact
  letI : SimplyConnectedSpace I.parent.carrier.carrier := I.parent_simply_connected
  letI : SimplyConnectedSpace I.child.carrier.carrier := I.child_simply_connected
  obtain ⟨parent⟩ := P (M := I.parent.carrier.carrier)
  obtain ⟨child⟩ := P (M := I.child.carrier.carrier)
  obtain ⟨eX⟩ := parent.homotopy_three_sphere
  obtain ⟨eY⟩ := child.homotopy_three_sphere
  exact exists_homotopyEquiv_of_homotopy_three_spheres eX eY Q.map
    (comparison_homology_bijective Q)

end PoincareConjecture.M40
