import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Limit.Finite.LimitFiniteSliceChart
import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Spacetime.GeneralizedCylinderRestriction

/-!
# The actual retained future cylinder in the physical history

The selected M33 conversion keeps the original source, normalization,
maps and both metric slots on a fixed exhaustion region. MT Proposition
17.1; limit-finite-retained-endpoint.md, Z1.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M47

variable (F : ℕ → SurgeryFlowData.{u}) (W : ∀ k, M33RegularHistoryWindow (F k))
  (history : ∀ k, M33RegularHistoryData (W k)) (baseTime : ℕ → ℝ)
  (hbaseTime : ∀ k, baseTime k ∈ (history k).generalized.interval)
  (basePoint : ∀ k, ((history k).generalized.slice (baseTime k)).carrier)
  (hPositive : ∀ k, 0 < ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k)))
  (hDiverges : Tendsto (fun k => ((F k).connection (baseTime k)).scalarCurvature
    ((history k).history.forward (baseTime k) (hbaseTime k) (basePoint k))) atTop atTop)

local notation "V" => regularHistoryBlowupSequence F W history baseTime hbaseTime
  basePoint hPositive hDiverges

variable {J : Set ℝ} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges) J)

private local instance retainedCylinderTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance retainedCylinderCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance retainedCylinderManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

/-- The actual restricted convergence cylinder converts to physical maps
on the same source and clock, preserving both metric differential slots. -/
theorem limitFinite_retained_physical_cylinder
    (j k : ℕ) {c : ℝ}
    (hI : Icc c 0 ⊆ Icc (-G.exhaustion.time k) 0)
    (hU : G.exhaustion.space j ⊆ G.exhaustion.space k) :
    ∃ e : SurgeryFlowCylinder (F (G.subsequence k)) G.limit.sliceCarrier
        (baseTime (G.subsequence k)) ((V).scale (G.subsequence k))
        (Icc c 0) (G.exhaustion.space j),
      (∀ s (hs : s ∈ Icc c 0), ∀ x ∈ G.exhaustion.space j,
        e.forward s hs x = (history (G.subsequence k)).history.forward
          (baseTime (G.subsequence k) + s / (V).scale (G.subsequence k))
          (limitNoncollapse_physical_time_mem G k s (hI hs))
          ((G.embedding k).forward s (hI hs) x)) ∧
      (∀ s (hs : s ∈ Icc c 0), ∀ x ∈ G.exhaustion.space j,
        ∀ v w : TangentSpace (𝓡 3) x,
          e.pullbackInner s hs x v w = (G.embedding k).pullbackInner s (hI hs) x v w) := by
  let e := (G.embedding k).restrict hI hU
  exact (history (G.subsequence k)).cylinders_to_surgery G.limit.sliceCarrier
    (baseTime (G.subsequence k)) ((V).scale (G.subsequence k)) (Icc c 0)
    (G.exhaustion.space j) ordConnected_Icc (G.exhaustion.space_open j)
    (fun s hs => limitNoncollapse_physical_time_mem G k s (hI hs)) e

end PoincareMT.M47
