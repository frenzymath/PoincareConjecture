import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.ParabolicRescaling
import PoincareLib.Geometry.RicciFlow.Surgery.StandardCap.Persistence.SourceNames.Homothety
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Compat.GeneralizedEquation
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.PhysicalBirthMetric
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.LGeometry.CapEntry.PersistenceWindow
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.SliceGeometry.GeneralizedSlices

/-!
# The persistence estimates on the actual history cylinder

Proposition 16.13, pp. 377-378. The zeroth comparison and scalar
readout concern the original M44 cylinder. These identities transport
them to the exact generalized cylinder returned by M33, on the full
physical source ball and with its actual scale.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.Proofs.M12
end PoincareMT.Proofs.M12
open PoincareMT.EpochExtension.Spacetime
namespace PoincareMT.M13
export PoincareMT.EpochExtension.SliceGeometry (originalSlice_scalar)
end PoincareMT.M13

namespace PoincareMT.Proofs.M46

open PoincareMT.Proofs.M12

/-- The model birth comparison bounds the actual normalized physical
metric in every tangent direction. Source: Proposition 16.13, p. 378. -/
theorem capCylinder_physicalBirth_lower
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hT).cap_count} {A eta mu : ℝ} {I : Set ℝ}
    {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ I) (hbase : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    {s : ℝ} (hs : s ∈ I)
    (hbound : ∀ x ∈ F.standard_initial.metric.ball 0 A, ∀ v : StandardCapSpace,
      mu * capComparisonCoefficients e initial.chart 0 hzero x v v ≤
        capComparisonCoefficients e initial.chart s hs x v v)
    {y : (F.slice t).carrier} (hy : y ∈ U) (v : TangentSpace (𝓡 3) y) :
    ((F.parameters.h t)⁻¹ ^ 2) * (mu * (F.metric t).inner y v v) ≤
      e.pullbackInner s hs y v v := by
  have hU : IsOpen U := by
    rw [← comparison.choose_spec.2.2.2.1]
    exact (capInitialPartialDiffeomorph initial).open_target
  have h := capComparison_birth_lower_on_physical_ball e initial comparison hzero hs
    hbound hy v
  rw [surgeryCylinder_pullbackInner_zero hU e hzero hbase hy v v] at h
  convert h using 1
  ring

/-- The exact image of the comparison chart transfers its pointwise
scalar lower bound to every point of the physical birth ball.
Source: Definition 16.12 and Proposition 16.13, pp. 376-378. -/
theorem capCylinder_physicalScalar_lower
    {F : SurgeryFlowData.{u}} {S : MaximalStandardCapFlow F.standard_initial}
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hT).cap_count} {A eta bound : ℝ} {I : Set ℝ}
    {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) I U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F S A eta e initial.chart)
    {s : ℝ} (hs : s ∈ I)
    (hbound : ∀ x ∈ F.standard_initial.metric.ball 0 A,
      bound ≤ (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
        (e.forward s hs (initial.chart x)))
    {y : (F.slice t).carrier} (hy : y ∈ U) :
    bound ≤ (F.connection (t + s / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (e.forward s hs y) := by
  obtain ⟨x, hx, rfl⟩ := comparison.choose_spec.2.2.2.1.symm ▸ hy
  exact hbound x hx

/-- M33's literal cylinder forward-map equality gives equality of
the actual physical and realized scalar curvatures, at the same
normalized parameter. Source: Proposition 14.12, p. 350. -/
theorem historyCylinder_scalar_pullback
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) (G : FlowBoxRicciGeometry H.generalized)
    (hM13 : GeneralizedParabolicRescalingTheory.{u} 3)
    {origin scale : ℝ} {I J : Set ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (d : GeneralizedFlowCylinder H.generalized (F.slice origin) origin scale J U)
    (hJI : J ⊆ I)
    (htime : ∀ s ∈ J, origin + s / scale ∈ H.generalized.interval)
    (hforward : ∀ s hs x, x ∈ U →
      H.history.forward (origin + s / scale) (htime s hs) (d.forward s hs x) =
        e.forward s (hJI hs) x)
    {s : ℝ} (hs : s ∈ J) {x : (F.slice origin).carrier} (hx : x ∈ U) :
    horizontalScalarCurvature G.toLGeometry.leafwise (d.pointMap s hs x) =
      (F.connection (origin + s / scale)).scalarCurvature (e.forward s (hJI hs) x) := by
  change horizontalScalarCurvature G.leafwise
    (⟨origin + s / scale, d.forward s hs x⟩ : H.generalized.point) = _
  rw [M13.originalSlice_scalar G hM13, ← H.scalar_pullback _ (htime s hs),
    hforward s hs x hx]

end PoincareMT.Proofs.M46
