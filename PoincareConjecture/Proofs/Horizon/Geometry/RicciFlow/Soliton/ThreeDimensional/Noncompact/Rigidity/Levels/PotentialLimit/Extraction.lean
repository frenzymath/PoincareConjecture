import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Estimates
import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.SmoothCompactness








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.secondCountable FlowCarrier.t3Space
attribute [local instance] RicciFlow.smallCarrier RicciFlow.smallChartedSpace
  RicciFlow.smallIsManifold

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {S : GradientShrinkingSolitonData 3 M} (G : ShrinkingSolitonFlow S) {q : ℕ → M}
  (L : AncientPointedGeometricConvergence
    (fun _ => AncientRescalingSequence.smallRescalingCarrier (M := M))
    (fun _ => G.unscaledSourceFlow.shrink.metric)
    (fun k => equivShrink M (q k)) 1)

theorem exists_normalizedPotentialPullback_smooth_limit
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : MetricComplete (L.limitFlow.metric 0)) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧ ∃ b : L.limitCarrier.carrier → ℝ,
      ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ b ∧ b L.base = 0 ∧
      (∀ x, Tendsto (fun k => G.normalizedPotentialPullback L (σ k) x) atTop (𝓝 (b x))) ∧
      ∀ (z : L.limitCarrier.carrier) (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))),
        IsCompact K → K ⊆ (extChartAt (𝓡 3) z).target →
        TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            (G.normalizedPotentialPullback L (σ k) ∘ (extChartAt (𝓡 3) z).symm))
          (iteratedFDeriv ℝ m (b ∘ (extChartAt (𝓡 3) z).symm)) atTop K := by
  obtain ⟨σ, hσ, b, hb, hp, hj⟩ :=
    Poincare.Manifold.exists_smooth_subsequence_of_locallyEventuallyBounded_chart_derivatives
      (G.normalizedPotentialPullback L)
      (G.normalizedPotentialPullback_coordinate_locally_smooth L)
      (G.normalizedPotentialPullback_coordinate_derivatives_bounded L hD p hescape hcomplete)
  refine ⟨σ, hσ, b, hb, ?_, hp, hj⟩
  apply tendsto_nhds_unique (hp L.base)
  simpa only [G.normalizedPotentialPullback_base L] using
    (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end PoincareConjecture.ShrinkingSolitonFlow
