import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.CylinderBounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.Compactness.Relative.UniformExtraction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology NNReal

universe u

namespace PoincareConjecture.AncientCompactTimeConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space FlowCarrier.measurableSpace FlowCarrier.borelSpace
  FlowCarrier.secondCountable

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {S : AncientRescalingSequence K}

theorem exists_reducedLengthPullback_common_uniformSubsequence
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : ℕ → G.limit.carrier.carrier) (a : ℕ → EuclideanSpace ℝ (Fin n))
    (r α β : ℕ → ℝ) (hr : ∀ i, 0 < r i) (hα : ∀ i, 0 < α i)
    (hαβ : ∀ i, α i ≤ β i)
    (hchart : ∀ i, Metric.closedBall (a i) (2 * r i) ⊆
      (chartAt (EuclideanSpace ℝ (Fin n)) (q i)).target) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ f : ∀ i, (Metric.closedBall (a i) (r i) ×ˢ Icc (α i) (β i)) → ℝ,
        (∀ i, Continuous (f i)) ∧ ∀ i,
          TendstoUniformly
            (fun k z => G.reducedLengthPullback (σ k)
              ((chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm z.val.1) z.val.2)
            (f i) atTop := by
  let X (i : ℕ) := Metric.closedBall (a i) (r i) ×ˢ Icc (α i) (β i)
  let (i : ℕ) : CompactSpace (X i) := isCompact_iff_compactSpace.mp
    ((isCompact_closedBall (a i) (r i)).prod isCompact_Icc)
  choose D C hC hgood using fun i =>
    G.reducedLengthPullback_eventually_lipschitz_on_chart_cylinder P (q i)
      (hr i) (hα i) (hαβ i) (hchart i)
  apply PointedGeometricConvergence.exists_common_uniformSubsequence_of_eventually_lipschitz
    (fun i k (z : X i) => G.reducedLengthPullback k
      ((chartAt (EuclideanSpace ℝ (Fin n)) (q i)).symm z.val.1) z.val.2)
    D (0 : ℝ) (fun i => Icc 0 (C i)) (fun _ => isCompact_Icc)
  intro i
  filter_upwards [hgood i] with k hk
  exact ⟨fun x y => hk.1 x.property y.property, fun z => hk.2 z.val z.property⟩

end PoincareConjecture.AncientCompactTimeConvergence
