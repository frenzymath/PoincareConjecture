import PoincareConjecture.Proofs.M47.LimitFiniteEndpointCurvature
import PoincareConjecture.Proofs.M47.LimitFiniteCompactBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Filter Set
open scoped ENNReal Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

local notation "E" => EuclideanSpace ℝ (Fin 3)

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

private local instance finiteEndpointCompactTopology :
    TopologicalSpace G.limit.carrier.carrier := G.limit.carrier.topologicalSpace
private local instance finiteEndpointCompactCharts :
    ChartedSpace E G.limit.carrier.carrier := G.limit.carrier.chartedSpace
private local instance finiteEndpointCompactManifold :
    IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold

local notation "U" => (fun m : ℕ => TopologicalSpace.Opens.mk
  (G.exhaustion.space m) (G.exhaustion.space_open m))

theorem limitFinite_compact_endpoint_curvature_bound
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
    (d : ℕ → ℝ) (hd : ∀ m, 0 < d m)
    (A : ∀ m, RicciFlow 3 (U m) (Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4)))
    (gE : RiemannianMetric 3 G.limit.sliceCarrier.carrier) (DE : LeviCivitaData gE)
    (hendpoint : ∀ m (x : U m) (v w : E),
      ((A m).metric (-H.toReal)).inner x v w = gE.inner x.val
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    (hold : ∀ m t, t ∈ Ioo (-H.toReal - d m / 8) (-H.toReal + d m / 4) →
      t ∈ blowupBackwardInterval H → ∀ (x : U m) (v w : E),
        ((A m).metric t).inner x v w = (G.limit.flow.metric t).inner x.val
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x v)
          (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U m → G.limit.sliceCarrier.carrier) x w))
    {X : Set G.limit.carrier.carrier} (hX : IsCompact X) :
    ∃ K : ℝ, 1 ≤ K ∧
      (∀ t ∈ blowupBackwardInterval H, ∀ x ∈ X,
        (G.limit.flow.connection t).scalarCurvature x ≤ K ∧
          (G.limit.flow.connection t).curvatureTensorNorm x ≤ 9 * K) ∧
      ∀ x ∈ X, DE.scalarCurvature x ≤ K ∧ DE.curvatureTensorNorm x ≤ 9 * K := by
  obtain ⟨K, hK, hbound⟩ := limitFinite_compact_curvature_bound F W history baseTime
    hbaseTime basePoint hPositive hDiverges G P schedules hH hfinite hepsilon hsmall
    hroundSmall hepsilon₀ hC hParameters hPinched rNext hThreshold hEarlier hterminal hX
  exact ⟨K, hK, hbound,
    limitFinite_endpoint_bounds G d A gE DE hendpoint hold hfinite hd hbound⟩

end PoincareConjecture.M47
