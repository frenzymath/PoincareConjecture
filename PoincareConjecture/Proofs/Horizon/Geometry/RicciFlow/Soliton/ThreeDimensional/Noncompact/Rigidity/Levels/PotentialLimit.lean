import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Extraction
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Noncompact.Rigidity.Levels.PotentialLimit.Identities
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Splitting.ParallelGradient.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.ShrinkingSolitonFlow

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold FlowCarrier.t3Space
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

structure NormalizedPotentialLimit where
  subsequence : ℕ → ℕ
  subsequence_strictMono : StrictMono subsequence
  potential : L.limitCarrier.carrier → ℝ
  potential_contMDiff : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ potential
  potential_base : potential L.base = 0
  unitGradient : RiemannianMetric.HasUnitGradient (L.limitFlow.connection 0) potential
  zeroHessian : RiemannianMetric.HasZeroHessian (L.limitFlow.connection 0) potential
  potential_tendsto : ∀ x,
    Tendsto (fun k => G.normalizedPotentialPullback L (subsequence k) x)
      atTop (𝓝 (potential x))
  potential_jets_tendsto :
    ∀ (z : L.limitCarrier.carrier) (m : ℕ) (K : Set (EuclideanSpace ℝ (Fin 3))),
      IsCompact K → K ⊆ (extChartAt (𝓡 3) z).target →
      TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (G.normalizedPotentialPullback L (subsequence k) ∘ (extChartAt (𝓡 3) z).symm))
        (iteratedFDeriv ℝ m (potential ∘ (extChartAt (𝓡 3) z).symm)) atTop K

theorem exists_normalizedPotentialLimit
    (hD : S.connection.CurvatureTensorCalculus) (p : M)
    (hescape : Tendsto (fun k => (S.metric.edist p (q k)).toReal) atTop atTop)
    (hcomplete : MetricComplete (L.limitFlow.metric 0)) :
    Nonempty (G.NormalizedPotentialLimit L) := by
  obtain ⟨σ, hσ, b, hb, hbase, hp, hj⟩ :=
    G.exists_normalizedPotentialPullback_smooth_limit L hD p hescape hcomplete
  obtain ⟨_, hu, hz⟩ := G.normalizedPotential_limit_identities L hj hσ hD p hescape hb
  exact ⟨⟨σ, hσ, b, hb, hbase, hu, hz, hp, hj⟩⟩

theorem normalizedPotentialPullback_eq_zero_iff
    (k : ℕ) (hscale : S.potentialGradientScale (q (L.subsequence k)) ≠ 0)
    (x : L.limitCarrier.carrier) :
    G.normalizedPotentialPullback L k x = 0 ↔
      S.potential (G.unscaledOriginalEmbedding L k x) = S.potential (q (L.subsequence k)) := by
  simp only [normalizedPotentialPullback, GradientShrinkingSolitonData.normalizedPotential,
    div_eq_zero_iff, hscale, or_false, sub_eq_zero]

end PoincareConjecture.ShrinkingSolitonFlow
