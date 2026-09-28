import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.LimitGradient.Source
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Asymptotic.ReducedLength.Extraction.Ancient.Charts


noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology NNReal ENNReal

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

theorem eventually_reducedLengthPullback_gradient_energy_bound
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let f := fun k x => G.reducedLengthPullback k (e x) τ
    ∀ᶠ k in atTop, ∀ᵐ x ∂volume, x ∈ A →
      fderiv ℝ (f k) x
          ((((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackCoefficients
            (G.sourceCoordinateChart k q) x).inverse (fderiv ℝ (f k) x)) ≤
        3 * f k x / τ := by
  filter_upwards [G.eventually_subset_sourceCoordinateChart q hA hchart,
    eventually_timeWindow_mem_nhds (by norm_num : (-1 : ℝ) < 0)] with k hk hbase
  obtain ⟨he, hei⟩ := G.sourceCoordinateChart_smooth k q
  have hf : (fun x => reducedLength K.flow 0 S.reference
      (G.sourceCoordinateChart k q x) (S.scale (G.subsequence k) * τ)) =
      (fun x => G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ) := by
    funext x
    rw [G.sourceCoordinateChart_apply k q hbase]
    rfl
  have h := (S.rescaling (G.subsequence k)).reducedLength_coordinate_gradient_bound_ae
    P S.reference hτ (G.sourceCoordinateChart k q) he hei
  dsimp only at h ⊢
  rw [hf] at h
  filter_upwards [h] with x hx hxs
  have hval : reducedLength K.flow 0 S.reference (G.sourceCoordinateChart k q x)
      (S.scale (G.subsequence k) * τ) = G.reducedLengthPullback k
        ((chartAt (EuclideanSpace ℝ (Fin n)) q).symm x) τ := congrFun hf x
  simpa only [hval] using hx (hk hxs)

theorem eventually_reducedLengthPullback_weighted_gradient_energy_bound
    (G : AncientCompactTimeConvergence S) (P : AncientAsymptoticSolitonPredecessors K)
    (q : G.limit.carrier.carrier) {A : Set (EuclideanSpace ℝ (Fin n))}
    (hA : IsCompact A) (hchart : A ⊆ (chartAt (EuclideanSpace ℝ (Fin n)) q).target)
    {τ : ℝ} (hτ : 0 < τ) :
    let e := (chartAt (EuclideanSpace ℝ (Fin n)) q).symm
    let f := fun k x => G.reducedLengthPullback k (e x) τ
    let ρ := fun k x =>
      ((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackVolumeDensity
        (G.sourceCoordinateChart k q) x
    ∀ᶠ k in atTop, ∀ᵐ x ∂volume, x ∈ A →
      ρ k x * fderiv ℝ (f k) x
          ((((S.rescaling (G.subsequence k)).flow.metric (-τ)).pullbackCoefficients
            (G.sourceCoordinateChart k q) x).inverse (fderiv ℝ (f k) x)) ≤
        ρ k x * (3 * f k x / τ) := by
  filter_upwards [G.eventually_reducedLengthPullback_gradient_energy_bound P q hA hchart hτ]
    with k hk
  filter_upwards [hk] with x hx hxs
  exact mul_le_mul_of_nonneg_left (hx hxs) (Real.sqrt_nonneg _)

end PoincareConjecture.AncientCompactTimeConvergence
