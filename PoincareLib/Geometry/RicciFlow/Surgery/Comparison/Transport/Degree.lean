import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Theory
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Transport.Retained
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Topology.LocalDegree
/-!
# Degree of the actual selected comparison map

Morgan-Tian pp. 430-431 and the retained-local-degree section of the
2026-09-18 SurgeryComparison.Transport contract. The unique retained fiber makes the actual H3 map
invertible; transporting the parent orientation through its inverse gives
degree one, including when the local retained chart reverses orientation.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.SurgeryComparison.Transport

/-- Homotopic maps induce the same actual integral H3 map. This is the
degree invariance used for the approximants in Claim 18.22, p. 433. -/
theorem surgeryThirdHomologyMap_eq_of_homotopic
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (h : ContinuousMap.Homotopic f g) :
    surgeryThirdHomologyMap f = surgeryThirdHomologyMap g := by
  let H : TopCat.Homotopy (TopCat.ofHom f) (TopCat.ofHom g) := Classical.choice h
  exact congrArg (fun k => k.hom)
    (H.congr_homologyMap_singularChainComplexFunctor
      (ModuleCat.of ℤ (ULift.{u} ℤ)) 3)

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {T : ℝ} {hT : T ∈ D.flow.surgery_times}
  [Nonempty (D.flow.slice T).carrier]
  {I : RepairedComparisonHomotopyInput D T hT}
  (Q : RepairedComparisonMapConclusion I.toRepairedComparisonMapInput)

/-- The induced H3 map is bijective by its singleton retained fiber.
This is the degree calculation of Morgan-Tian pp. 430-431. -/
theorem comparison_homology_bijective :
    Function.Bijective (surgeryThirdHomologyMap Q.map) := by
  let : CompactSpace I.parent.carrier.carrier :=
    isCompact_univ_iff.mp I.parent.compact
  let : CompactSpace I.child.carrier.carrier :=
    isCompact_univ_iff.mp I.child.compact
  let : SimplyConnectedSpace I.parent.carrier.carrier := I.parent_simply_connected
  let : SimplyConnectedSpace I.child.carrier.carrier := I.child_simply_connected
  obtain ⟨x, hx, huniq⟩ := exists_unique_retained_fiber Q
  exact PoincareMT.SurgeryComparison.Topology.integralThirdHomologyMap_bijective_of_unique_preimage
    Q.map x (retainedOpenPartialHomeomorph Q) hx (fun _ _ => rfl) huniq

/-- The linear equivalence has exactly the actual induced comparison map
as its forward function; Morgan-Tian pp. 430-431. -/
noncomputable def comparisonHomologyEquiv :
    surgeryThirdHomology I.parent.carrier.carrier ≃ₗ[ℤ]
      surgeryThirdHomology I.child.carrier.carrier :=
  LinearEquiv.ofBijective (surgeryThirdHomologyMap Q.map)
    (comparison_homology_bijective Q)

/-- Choose the child orientation by transporting the given parent
orientation through the inverse comparison map; Morgan-Tian pp. 430-431. -/
noncomputable def comparisonChildOrientation :
    surgeryThirdHomology I.child.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ :=
  (comparisonHomologyEquiv Q).symm.trans I.parent_orientation

/-- The selected orientation gives degree one for every parent class,
with the variance required in the SurgeryComparison.Transport contract; Morgan-Tian pp. 430-431. -/
theorem comparison_degree_one (z : surgeryThirdHomology I.parent.carrier.carrier) :
    comparisonChildOrientation Q (surgeryThirdHomologyMap Q.map z) =
      I.parent_orientation z := by
  change I.parent_orientation
    ((comparisonHomologyEquiv Q).symm (comparisonHomologyEquiv Q z)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Every homotopic approximant retains degree one for the fixed child
orientation, as required for Claim 18.22, Morgan-Tian p. 433. -/
theorem comparison_degree_one_of_homotopic
    {f : C(I.parent.carrier.carrier, I.child.carrier.carrier)}
    (hf : ContinuousMap.Homotopic f Q.map)
    (z : surgeryThirdHomology I.parent.carrier.carrier) :
    comparisonChildOrientation Q (surgeryThirdHomologyMap f z) =
      I.parent_orientation z := by
  rw [surgeryThirdHomologyMap_eq_of_homotopic hf]
  exact comparison_degree_one Q z

end PoincareMT.SurgeryComparison.Transport
