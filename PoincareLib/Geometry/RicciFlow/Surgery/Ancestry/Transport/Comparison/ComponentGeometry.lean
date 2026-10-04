import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.ComponentMetric
import PoincareLib.AlgebraicTopology.HomotopyGroup.LoopSpace.Compatibility.ThreeManifoldTopology

/-!
# Geometry and orientation of the selected components

The component restrictions in Morgan--Tian Proposition 15.12 (p. 365)
use the actual ambient metrics. The integral orientation and point paths
are the inputs to the class transport on pp. 430-431.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- The metric restriction of Proposition 15.12, p. 365, on the supplied component. -/
noncomputable def m57ComponentMetric
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier) : RiemannianMetric 3 C.carrier.carrier :=
  (Classical.choice (m39ComponentMetric C g)).val

/-- The selected restriction has the exact pullback required on p. 365. -/
theorem m57ComponentMetric_pullback
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (g : RiemannianMetric 3 A.carrier) (x : C.carrier.carrier)
    (v w : TangentSpace (𝓡 3) x) :
    g.inner (C.inclusion x) (mfderiv (𝓡 3) (𝓡 3) C.inclusion x v)
      (mfderiv (𝓡 3) (𝓡 3) C.inclusion x w) =
        (m57ComponentMetric C g).inner x v w :=
  (Classical.choice (m39ComponentMetric C g)).property x v w

/-- The selected parent's integral orientation for pp. 430-431, using M02's
top homology calculation with the identical lifted integer coefficient. -/
theorem m57ComponentOrientation
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    [SimplyConnectedSpace C.carrier.carrier] :
    Nonempty (surgeryThirdHomology C.carrier.carrier ≃ₗ[ℤ] ULift.{u} ℤ) := by
  let : CompactSpace C.carrier.carrier := ⟨C.compact⟩
  obtain ⟨e⟩ :=
    Proofs.M02.Topology.nonempty_integralThreeManifoldTop_equiv_int C.basepoint
  exact ⟨e.trans ULift.moduleEquiv.symm⟩

/-- Genuine point paths in the selected component, as required by Definition
18.2, pp. 419-420, and the based class transport on pp. 430-431. -/
theorem m57ComponentPointPath
    {A : GeneralizedSliceCarrier.{u}} (C : SurgerySelectedComponent A)
    (x y : C.carrier.carrier) : Nonempty (Path x y) := by
  let : ConnectedSpace C.carrier.carrier := connectedSpace_iff_univ.mpr C.connected
  let : LocallyPathConnectedSpace C.carrier.carrier :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier.carrier
  let : PathConnectedSpace C.carrier.carrier :=
    PathConnectedSpace.of_locallyPathConnectedSpace
  exact ⟨PathConnectedSpace.somePath x y⟩

end PoincareMT
