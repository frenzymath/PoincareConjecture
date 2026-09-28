import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.GradientGrowth
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Flow.LinearGrowth

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem exists_compact_negative_potential_gradient_confinement_on_Icc
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B)
    (a b : ℝ) (hb : b < 0) (s : ℝ) (hs : s ∈ Icc a b)
    (x : L.convergence.limit.carrier.carrier) :
    ∃ Kc : Set L.convergence.limit.carrier.carrier, IsCompact Kc ∧
      ∀ (I : Set ℝ), IsOpen I → Convex ℝ I → s ∈ I →
      ∀ (γ : ℝ → L.convergence.limit.carrier.carrier), γ s = x →
        ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) ∞ γ I →
        (∀ t ∈ I, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) γ t
          ((1 : ℝ →L[ℝ] ℝ).smulRight
            (-((L.convergence.limit.flow.connection t).gradient
              (fun y => L.potential (y, t)) (γ t))))) →
        ∀ t ∈ I ∩ Icc a b, γ t ∈ Kc := by
  let : ConnectedSpace L.convergence.limit.carrier.carrier :=
    connectedSpace_iff_univ.mpr L.convergence.limit.carrier.connected
  obtain ⟨A, hA, hgrowth⟩ := L.exists_negative_potential_gradient_linear_growth_on_Icc
    hC hbound a b hb s hs
  exact (L.convergence.limit.flow.metric s).exists_compact_confinement_of_linear_growth
    (L.convergence.limit.complete s (hs.2.trans_lt hb)) L.convergence.limit.base x
    hs hA.le hgrowth

end PoincareConjecture.AncientAsymptoticSolitonLimitData
