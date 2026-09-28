import PoincareConjecture.Proofs.M47.LimitNoncollapseCompactScalar
import PoincareConjecture.Proofs.M47.LimitNoncollapseCompactMinimum

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

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
  {H : ℝ≥0∞} (G : GeneralizedBlowupConvergence
    (regularHistoryBlowupSequence F W history baseTime hbaseTime basePoint hPositive hDiverges)
    (blowupBackwardInterval H))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

theorem limitFinite_compact_carrier_curvature_bound
    (P : M47Predecessors.{u}) (schedules : RepairedControlledSchedulesData.{u})
    (hH : 0 < H) (hfinite : H ≠ ⊤) {epsilon C : ℝ}
    (hepsilon : 0 < epsilon) (hepsilon₀ : epsilon ≤ schedules.calibration.epsilon₁₀)
    (hC : 0 < C)
    (hParameters : ∀ k, (F k).parameters.epsilon = epsilon ∧ (F k).parameters.C = C)
    (hPinched : ∀ k, ∀ s ∈ (W k).interval, SurgeryPinchedAt ((F k).connection s) s)
    (rNext : ℕ → ℝ)
    (hThreshold : ∀ k, (rNext k)⁻¹ ^ 2 ≤
      (regularHistoryBlowupSequence F W history baseTime hbaseTime
        basePoint hPositive hDiverges).scale k)
    (hEarlier : ∀ k, SurgeryCanonicalOn (F k) (Ico 0 (baseTime k)) (rNext k))
    {B0 : ℝ} (hterminal : ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection 0).curvatureTensorNorm x ≤ B0)
    (hcompact : IsCompact (univ : Set G.limit.carrier.carrier)) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t ∈ blowupBackwardInterval H, ∀ x : G.limit.carrier.carrier,
      (G.limit.flow.connection t).scalarCurvature x ≤ K ∧
        (G.limit.flow.connection t).curvatureTensorNorm x ≤ 9 * K := by
  let : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace
  let : T2Space G.limit.carrier.carrier := G.limit.carrier.t2Space
  have hlow : ∀ t ∈ blowupBackwardInterval H, ∃ y ∈ (univ : Set G.limit.carrier.carrier),
      (G.limit.flow.connection t).scalarCurvature y ≤ 1 := by
    intro t ht
    obtain ⟨y, hy⟩ := limitNoncollapse_compact_exists_low_point P.m04 G.limit hcompact t ht
    exact ⟨y, mem_univ y, hy⟩
  obtain ⟨K, hK, hbound⟩ := limitFinite_compact_scalar_bound F W history baseTime hbaseTime
    basePoint hPositive hDiverges G P schedules hH hfinite hepsilon hepsilon₀ hC hParameters
    hPinched rNext hThreshold hEarlier hterminal hcompact isPreconnected_univ hlow
  refine ⟨K, hK, ?_⟩
  intro t ht x
  have hx := hbound t ht x (mem_univ x)
  refine ⟨hx, ?_⟩
  have hnorm := (G.limit.flow.connection t).curvatureTensorNorm_le_scalarCurvature
    (P.m04.tensor_calculus 3 G.limit.carrier.carrier
      (G.limit.flow.metric t) (G.limit.flow.connection t)) x
    (G.limit.nonnegative_curvature_operator t ht x)
  norm_num only [Nat.cast_ofNat, OfNat.ofNat, show (3 : ℝ) ^ 2 = 9 by norm_num] at hnorm
  exact hnorm.trans (mul_le_mul_of_nonneg_left hx (by norm_num))

end PoincareConjecture.M47
