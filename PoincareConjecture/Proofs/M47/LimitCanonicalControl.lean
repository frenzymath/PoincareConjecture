import PoincareConjecture.Proofs.M47.LimitCanonicalNeckControl
import PoincareConjecture.Proofs.M47.LimitCanonicalCapControl
import PoincareConjecture.Proofs.M47.LimitCanonicalComponentControl
import PoincareConjecture.Proofs.M47.LimitCanonicalRoundControl









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M47

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

variable (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime
    basePoint hPositive hDiverges) (blowupBackwardInterval ⊤))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : MeasurableSpace G.limit.carrier.carrier := G.limit.carrier.measurableSpace
private local instance : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : SecondCountableTopology G.limit.carrier.carrier :=
  G.limit.carrier.secondCountable
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace



theorem limitCanonical_eventually_selected_control
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    {kappa : ℝ} (hkappa : 0 < kappa) (hnc : BlowupLimitNoncollapsed G.limit kappa) :
    ∀ᶠ k in atTop,
      SurgeryCanonicalControl (F (G.subsequence k)) (baseTime (G.subsequence k))
        ((history (G.subsequence k)).history.forward (baseTime (G.subsequence k))
          (hbaseTime (G.subsequence k)) (basePoint (G.subsequence k)))
        S.setup.epsilon S.setup.C := by
  let R : ∀ i, M33RegularHistoryRealization ((V).flow i) (F i) :=
    fun i => (history i).history
  obtain ⟨hcanonical, hC⟩ :=
    limitCanonical_ancient_alternative P.m04 S G F R hkappa hnc
  rcases hcanonical with ⟨N, hcenter⟩ | N | N | N
  · exact limitCanonical_eventually_neck_control F W history baseTime hbaseTime
      basePoint hPositive hDiverges G P
      (limitAncientIdentification P.m04 G.limit kappa hkappa hnc) N hcenter
  · filter_upwards [limitCanonical_eventually_cap_control P S G F R hkappa hnc hC N]
      with k hk
    exact hk.choose_spec
  · filter_upwards [limitCanonical_eventually_component_control P S G F R hkappa hnc hC N]
      with k hk
    exact hk.choose_spec
  · filter_upwards [limitCanonical_eventually_round_control P S G F R hkappa hnc N]
      with k hk
    exact hk.choose_spec

end PoincareConjecture.M47
