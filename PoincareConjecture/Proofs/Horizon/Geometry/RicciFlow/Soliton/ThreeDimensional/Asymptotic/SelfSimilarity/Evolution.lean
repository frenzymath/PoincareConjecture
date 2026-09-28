import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Flow.TimeDependent.Global
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.Confinement
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.SelfSimilarity.Regularity








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

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




theorem exists_negative_potential_gradient_evolution
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    (hbound : ∀ t : ℝ, t < 0 → ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : L.convergence.limit.carrier.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B) :
    ∃ E : ℝ → ℝ → L.convergence.limit.carrier.carrier → L.convergence.limit.carrier.carrier,
      (∀ s < 0, ∀ x, E s s x = x) ∧
      (∀ s < 0, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞
        (fun p : ℝ × L.convergence.limit.carrier.carrier => E s p.1 p.2) (Iio 0 ×ˢ univ)) ∧
      (∀ s < 0, ∀ x, ∀ t < 0, HasMFDerivAt 𝓘(ℝ, ℝ) (𝓡 3) (fun r => E s r x) t
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (-((L.convergence.limit.flow.connection t).gradient
            (fun y => L.potential (y, t)) (E s t x))))) ∧
      (∀ s < 0, ∀ t < 0, ∀ r < 0, ∀ x, E t r (E s t x) = E s r x) ∧
      (∀ s < 0, ∀ t < 0, Function.LeftInverse (E t s) (E s t) ∧
        Function.RightInverse (E t s) (E s t)) := by
  apply Poincare.Manifold.exists_smooth_global_timeDependentFlow_of_compact_confinement
    (n := 3) (M := L.convergence.limit.carrier.carrier)
    (X := fun t x => -((L.convergence.limit.flow.connection t).gradient
      (fun y => L.potential (y, t)) x))
    isOpen_Iio (convex_Iio 0) L.contMDiffOn_negative_potential_gradient
  intro s _ x a b hs hab
  exact L.exists_compact_negative_potential_gradient_confinement_on_Icc hC hbound
    a b (hab (right_mem_Icc.mpr (hs.1.trans hs.2))) s hs x

end PoincareConjecture.AncientAsymptoticSolitonLimitData
