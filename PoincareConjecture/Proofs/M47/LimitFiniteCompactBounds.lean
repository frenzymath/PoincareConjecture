import PoincareConjecture.Proofs.M47.LimitFiniteLowPoint
import PoincareConjecture.Proofs.M47.LimitNoncollapseCompactCarrier
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.Compactness.GeometricLimit.BoundaryCoverage

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
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

variable {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
  (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
  (blowupBackwardInterval H))

private local instance finiteCompactTopology : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance finiteCompactCharts : ChartedSpace
    (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteCompactManifold : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem limitFinite_compact_curvature_bound
    (P : M47Predecessors.{u}) (schedules : RepairedControlledSchedulesData.{u})
    (hH : 0 < H) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : 2 * epsilon < 1 / 2)
    (hroundSmall : epsilon ≤ 1 / 200)
    (hepsilon₀ : epsilon ≤ schedules.calibration.epsilon₁₀) (hC : 0 < C)
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (hPinched : ∀ k, ∀ s ∈ (W k).interval, SurgeryPinchedAt ((F k).connection s) s)
    (rNext : ℕ → ℝ) (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤ (V).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    {X : Set G.limit.carrier.carrier} (hX : IsCompact X) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t ∈ blowupBackwardInterval H, ∀ x ∈ X,
      (G.limit.flow.connection t).scalarCurvature x ≤ K ∧
        (G.limit.flow.connection t).curvatureTensorNorm x ≤ 9 * K := by
  classical
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  let : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  by_cases hcompact : IsCompact (univ : Set G.limit.carrier.carrier)
  · obtain ⟨K, hK, hbound⟩ := limitFinite_compact_carrier_curvature_bound
      F W history baseTime hbaseTime basePoint hPositive hDiverges G P schedules
      hH hfinite hepsilon hepsilon₀ hC hParameters hPinched rNext hThreshold
      hEarlier hterminal hcompact
    exact ⟨K, hK, fun t ht x _ => hbound t ht x⟩
  obtain ⟨y, c, _, hlow⟩ := limitFinite_exists_fixed_low_point F W history baseTime
    hbaseTime basePoint hPositive hDiverges G P hH hfinite hepsilon hsmall hroundSmall hC
    hParameters rNext hThreshold hEarlier hterminal hcompact
  let g0 := G.limit.flow.metric 0
  let := g0.toMetricSpace
  let := g0.properSpace_toMetricSpace (G.limit.complete 0 G.limit.zero_mem)
  obtain ⟨R, hR, hXR⟩ := hX.isBounded.subset_ball_lt 0 y
  let Y := closure (g0.ball y R)
  have hY : IsCompact Y := by
    dsimp only [Y]
    rw [← g0.toMetricSpace_ball]
    exact isBounded_ball.isCompact_closure
  have hYconnected : IsPreconnected Y := (g0.isPreconnected_ball y R).closure
  have hyY : y ∈ Y := by
    apply subset_closure
    rw [← g0.toMetricSpace_ball]
    exact mem_ball_self hR
  have hXY : X ⊆ Y := by
    intro x hx
    apply subset_closure
    rw [← g0.toMetricSpace_ball]
    exact hXR hx
  obtain ⟨K, hK, hbound⟩ := limitFinite_compact_scalar_bound F W history baseTime hbaseTime
    basePoint hPositive hDiverges G P schedules hH hfinite hepsilon hepsilon₀ hC hParameters
    hPinched rNext hThreshold hEarlier hterminal hY hYconnected
    (fun t ht => ⟨y, hyY, hlow t ht⟩)
  refine ⟨K, hK, ?_⟩
  intro t ht x hx
  have hscalar := hbound t ht x (hXY hx)
  refine ⟨hscalar, ?_⟩
  have hnorm := (G.limit.flow.connection t).curvatureTensorNorm_le_scalarCurvature
    (P.m04.tensor_calculus 3 G.limit.carrier.carrier
      (G.limit.flow.metric t) (G.limit.flow.connection t)) x
    (G.limit.nonnegative_curvature_operator t ht x)
  norm_num only [Nat.cast_ofNat, OfNat.ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left hscalar (by norm_num))

end PoincareConjecture.M47
