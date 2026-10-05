import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Degree
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Topology.DegreeHomotopySphere
/-!
# The homotopy equivalence of the selected comparison map

The authorized Poincare.Topology provider supplies homotopy three-sphere witnesses for
the actual parent and child.  The retained local degree calculation makes
the selected comparison map an isomorphism on integral H3.  Conjugation to
a universe-lifted standard sphere and the sphere-degree construction give
a homotopy inverse whose forward map is exactly the selected map.

Source: Morgan--Tian, printed pp. 430--431; the homotopy and based transport
section of the 2026-09-18 SurgeryComparison.Transport full contract.
-/

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology ContinuousMap

universe u

namespace PoincareMT.SurgeryComparison.Transport

/-- An actual H3 isomorphism between homotopy three-spheres has a homotopy
inverse with the given forward continuous map.  The sphere is lifted to the
component universe so the coefficient module remains exactly the contract's
`ULift Int`; Morgan--Tian pp. 430--431. -/
theorem exists_homotopyEquiv_of_homotopy_three_spheres
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (eX : X ≃ₕ ThreeSphere) (eY : Y ≃ₕ ThreeSphere)
    (f : C(X, Y)) (hbij : Function.Bijective (surgeryThirdHomologyMap f)) :
    ∃ e : X ≃ₕ Y, e.toFun = f := by
  let S := ULift.{u} ThreeSphere
  let eS : S ≃ₜ ThreeSphere := Homeomorph.ulift
  let EX : X ≃ₕ S := eX.trans eS.symm.toHomotopyEquiv
  let EY : Y ≃ₕ S := eY.trans eS.symm.toHomotopyEquiv
  apply SurgeryComparison.Topology.exists_homotopyEquiv_of_conjugate EX EY f
  apply SurgeryComparison.Topology.exists_homotopyEquiv_threeSphere_of_homology_bijective
    eS (EY.toFun.comp (f.comp EX.invFun))
  exact SurgeryComparison.Topology.homologyMap_bijective_conjugate EX EY f hbij

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonHomotopyInput D T hT}
  (Q : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput)

/-- The selected SurgeryComparison comparison map itself is the forward map of a
homotopy equivalence.  This uses only the authorized Poincare.Topology topology provider
and the local degree result, as in Morgan--Tian pp. 430--431. -/
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

end PoincareMT.SurgeryComparison.Transport
