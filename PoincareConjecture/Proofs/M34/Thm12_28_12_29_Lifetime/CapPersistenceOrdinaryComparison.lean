import PoincareConjecture.Proofs.M34.Thm12_28_12_29_Lifetime.CapOrdinaryEmbeddingSequence
import PoincareConjecture.Proofs.M34.Standard.GeneralizedCompactMetricComparison
import PoincareConjecture.Proofs.M34.Standard.QuadraticTangentComparison











set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M34

private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} {L : BlowupLimitFlow.{u} J} :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
  {I : SpacetimeInterval} {F : RicciFlow 3 M I.domain}
  (R : OrdinaryProductRicciGeometry F.metric I)

local notation "G" => ordinaryChapter11Flow (I := I) (F := F) R



theorem capPersistence_eventually_ordinary_tangent_comparison
    (p : ℕ → (G).point) (hp : ∀ k, 0 < (G).scalar (p k))
    (hd : Tendsto (fun k => (G).scalar (p k)) atTop atTop) {J : Set ℝ}
    (C : GeneralizedBlowupConvergence (fixedFlowBlowupSequence (G) p hp hd) J)
    {K : Set C.limit.sliceCarrier.carrier} (hK : IsCompact K) :
    ∀ᶠ k : ℕ in atTop, K ⊆ C.exhaustion.space k ∧
      let e := capOrdinaryEmbedding R p hp hd C k
      let h : RiemannianMetric 3 M := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
        ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))
      ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) ≤
          2 * (C.limit.flow.metric 0).tangentNorm x v ∧
        (C.limit.flow.metric 0).tangentNorm x v ≤
          2 * h.tangentNorm (e x) (mfderiv (𝓡 3) (𝓡 3) e x v) := by
  filter_upwards [C.eventually_pullback_inner_comparison_zero hK] with k hk
  refine ⟨hk.1, ?_⟩
  dsimp only
  intro x hx v
  let e := capOrdinaryEmbedding R p hp hd C k
  let h : RiemannianMetric 3 M := M13.scaleSmoothMetric (F.metric (p (C.subsequence k)).1)
    ((G).scalar (p (C.subsequence k))) (hp (C.subsequence k))
  let w := mfderiv (𝓡 3) (𝓡 3) e x v
  obtain ⟨hl, hu⟩ := hk.2 x hx v
  rw [capOrdinaryEmbedding_metric R p hp hd C k (hk.1 hx) v v] at hl hu
  have hupper : (1 / 2 : ℝ) * h.inner (e x) w w ≤
      (1 : ℝ) * (C.limit.flow.metric 0).inner x v v := by
    change h.inner (e x) w w ≤ 2 * (C.limit.flow.metric 0).inner x v v at hu
    linarith
  have hlower : (1 / 2 : ℝ) * (C.limit.flow.metric 0).inner x v v ≤
      (1 : ℝ) * h.inner (e x) w w := by simpa only [one_mul] using hl
  constructor
  · simpa only [Real.sqrt_one, mul_one] using
      h.tangentNorm_le_two_sqrt_mul_of_half_inner_le (C.limit.flow.metric 0)
        w v (by norm_num : (0 : ℝ) ≤ 1) hupper
  · simpa only [Real.sqrt_one, mul_one] using
      (C.limit.flow.metric 0).tangentNorm_le_two_sqrt_mul_of_half_inner_le h
        v w (by norm_num : (0 : ℝ) ≤ 1) hlower

end PoincareConjecture.M34
