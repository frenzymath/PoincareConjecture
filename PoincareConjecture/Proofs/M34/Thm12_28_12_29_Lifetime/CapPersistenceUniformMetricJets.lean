import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceLocalMetricJets
import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapPersistenceNeckSets

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

local notation "E₂" => EuclideanSpace ℝ (Fin 2)
local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace E₃ M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace E₃ L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

theorem ordinaryChapter11_eventually_neck_metricJets
    (p : ℕ → (G).point) (hp : ∀ k, 0 < (G).scalar (p k))
    (hd : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence (fixedFlowBlowupSequence (G) p hp hd) J)
    (hJ : UniqueDiffOn ℝ J) (N : EpsilonNeck (C.limit.flow.metric 0))
    (m : ℕ) (hm : m + 1 ≤ Nat.floor N.epsilon⁻¹)
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K) (hNK : N.carrier ⊆ K)
    (rho : ℝ) (hrho : 0 < rho) :
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧
      ∀ (q : UnitTwoSphere) (s : ℝ), s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∀ j ≤ m, ∀ i l : Fin 3,
        ‖iteratedFDeriv ℝ j (fun y =>
          roundCylinderTensorCoefficient
            (generalizedCylinderPullback (C.embedding k) N.coordinate_map 0)
            (chartAt E₂ q) y i l -
          roundCylinderTensorCoefficient
            (roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map)
            (chartAt E₂ q) y i l) (0, s)‖ < rho := by
  classical
  let P (k : ℕ) (q : UnitTwoSphere) (s : ℝ) : Prop :=
    ∀ j ≤ m, ∀ i l : Fin 3,
      ‖iteratedFDeriv ℝ j (fun y =>
        roundCylinderTensorCoefficient
          (generalizedCylinderPullback (C.embedding k) N.coordinate_map 0)
          (chartAt E₂ q) y i l -
        roundCylinderTensorCoefficient
          (roundCylinderPullback (C.limit.flow.metric 0) N.coordinate_map)
          (chartAt E₂ q) y i l) (0, s)‖ < rho
  have hlocal (a : C.limit.sliceCarrier.carrier) :
      ∃ U : Set C.limit.sliceCarrier.carrier, U ∈ 𝓝 a ∧
        ∀ᶠ k : ℕ in atTop, ∀ (q : UnitTwoSphere) (s : ℝ),
          s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ → N.coordinate_map (q, s) ∈ U → P k q s := by
    let c := extChartAt (𝓡 3) a
    obtain ⟨H, hH, haH, hHt⟩ := exists_compact_subset
      (isOpen_extChartAt_target (I := 𝓡 3) a) (mem_extChartAt_target (I := 𝓡 3) a)
    let U := c.source ∩ c ⁻¹' H
    have hU : U ∈ 𝓝 a := inter_mem (extChartAt_source_mem_nhds (I := 𝓡 3) a)
      ((continuousAt_extChartAt (I := 𝓡 3) a).preimage_mem_nhds
        (mem_interior_iff_mem_nhds.mp haH))
    refine ⟨U, hU, ?_⟩
    filter_upwards [ordinaryChapter11_eventually_chart_neck_metricJets
      R p hp hd C hJ N m hm a hH hHt rho hrho] with k hk q s hs hx
    exact hk q s hs hx.1 hx.2
  choose U hU hbound using hlocal
  obtain ⟨S, _, hcover⟩ := hK.elim_nhds_subcover U (fun a _ => hU a)
  obtain ⟨j0, hj0⟩ := C.exists_exhaustion_superset hK
  filter_upwards [S.eventually_all.mpr (fun a _ => hbound a), eventually_ge_atTop j0]
    with k hk hjk
  refine ⟨hj0.trans (C.exhaustion.space_increasing hjk), ?_⟩
  intro q s hs
  obtain ⟨a, haS, hxa⟩ : ∃ a ∈ S, N.coordinate_map (q, s) ∈ U a := by
    simpa only [mem_iUnion, exists_prop] using hcover (hNK (N.coordinate_map_mem_of_axial_mem hs))
  exact hk a haS q s hs hxa

end PoincareConjecture.M34
