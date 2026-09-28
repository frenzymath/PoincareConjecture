import PoincareConjecture.Definitions.M19TwoDimensionalClassification











set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]


inductive ThreeDimensionalSolitonModel
    (S : GradientShrinkingSolitonData 3 M)
    (G : ShrinkingSolitonFlow S) : Type (u + 2) where
  | compactRound : CompactRoundShrinkingModel G →
      ThreeDimensionalSolitonModel S G
  | sphereLine : SphereLineProductCertificate G →
      ThreeDimensionalSolitonModel S G
  | quotientSphereLine : QuotientSphereLineCertificate G →
      ThreeDimensionalSolitonModel S G

structure ThreeDimensionalSolitonConclusion
    (S : GradientShrinkingSolitonData 3 M) where
  flow : ShrinkingSolitonFlow S
  model : ThreeDimensionalSolitonModel S flow

structure ThreeDimensionalClassificationData
    (S : GradientShrinkingSolitonData 3 M) where
  conclusion : ThreeDimensionalSolitonConclusion S




structure ThreeDimensionalAsymptoticClassificationCertificate
    {K : AncientKappaSolution 3 M} (S : AncientRescalingSequence K)
    (L : AncientAsymptoticSolitonLimitData S) where
  bounded_curvature :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    ∀ t : ℝ, t < 0 →
      ∃ B : ℝ, 0 ≤ B ∧ ∀ x : C.carrier,
        |(L.convergence.limit.flow.connection t).curvatureTensorNorm x| ≤ B
  classified_flow :
    let C := L.convergence.limit.carrier
    letI : TopologicalSpace C.carrier := C.topologicalSpace
    letI : MeasurableSpace C.carrier := C.measurableSpace
    letI : BorelSpace C.carrier := C.borelSpace
    letI : ChartedSpace (EuclideanSpace ℝ (Fin 3)) C.carrier := C.chartedSpace
    letI : IsManifold (𝓡 3) ∞ C.carrier := C.isManifold
    letI : T2Space C.carrier := C.t2Space
    letI : T3Space C.carrier := C.t3Space
    letI : SecondCountableTopology C.carrier := C.secondCountable
    letI : PreconnectedSpace C.carrier := ⟨C.connected.isPreconnected⟩
    letI : Nonempty C.carrier := ⟨Classical.choose C.connected.nonempty⟩
    letI : ConnectedSpace C.carrier := ⟨inferInstance⟩
    ∃ (S₀ : GradientShrinkingSolitonData 3 C.carrier)
      (G : ShrinkingSolitonFlow S₀),
      S₀.metric = L.convergence.limit.flow.metric (-1) ∧
      G.flow = L.convergence.limit.flow ∧
      Nonempty (ThreeDimensionalSolitonModel S₀ G)

end PoincareConjecture
