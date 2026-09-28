import PoincareConjecture.Definitions.M18AsymptoticSoliton
import PoincareConjecture.Definitions.Ch09.ShrinkingSoliton









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


structure TwoDimensionalAncientRoundCertificate
    (K : AncientKappaSolution 2 M) where
  compact : CompactSpace M
  round_at_all_times : ∀ t : ℝ, t ≤ 0 →
    ConstantPositiveSectionalCurvature (K.flow.metric t) (K.flow.connection t)




structure TwoDimensionalAsymptoticRoundCertificate
    {K : AncientKappaSolution 2 M} (S : AncientRescalingSequence K)
    (L : AncientAsymptoticSolitonLimitData S) where
  bounded_curvature :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B
  self_similar :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      Nonempty (HomotheticMetricSlice
        (L.convergence.limit.flow.metric (-1))
        (L.convergence.limit.flow.metric t) |t|)
  compact :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    CompactSpace C.carrier
  round_at_all_times :
    ∀ t : ℝ, t < 0 →
      let C := L.convergence.limit.carrier
      letI : TopologicalSpace C.carrier := C.topologicalSpace
      letI : ChartedSpace (EuclideanSpace ℝ (Fin 2)) C.carrier := C.chartedSpace
      letI : IsManifold (𝓡 2) ∞ C.carrier := C.isManifold
      ConstantPositiveSectionalCurvature
        (L.convergence.limit.flow.metric t)
        (L.convergence.limit.flow.connection t)


inductive TwoDimensionalSolitonModel
    (S : GradientShrinkingSolitonData 2 M)
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | compactRound : CompactRoundShrinkingModel G → TwoDimensionalSolitonModel S G

structure TwoDimensionalShrinkingSolitonConclusion
    (S : GradientShrinkingSolitonData 2 M) where
  flow : ShrinkingSolitonFlow S
  model : TwoDimensionalSolitonModel S flow

end PoincareConjecture
