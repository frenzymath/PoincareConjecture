import PoincareConjecture.Definitions.Ch09.CanonicalNeighborhoods

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

def NoEmbeddedTrivialNormalProjectivePlane
    (_K : AncientKappaSolution 3 M) : Prop :=
  ¬ ∃ f : RealProjectiveTwo × Set.Ioo (-1 : ℝ) 1 → M,
    Topology.IsOpenEmbedding f

structure M26StrongTube (K : AncientKappaSolution 3 M) (t epsilon : ℝ)
    extends StrongTubeCertificate K t epsilon where
  tube_epsilon : tube.epsilon = epsilon
  carrier_eq_univ : tube.carrier = Set.univ

structure M26StrongCappedTube (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) extends StrongCappedTube K t epsilon C where
  tube_epsilon : tube.epsilon = epsilon
  strong_at : ∀ x ∈ tube.carrier, ∃ N : StrongEvolvingNeck K t epsilon,
    N.center = x
  cap_connection : cap.cap.connection = K.flow.connection t
  carrier_eq_univ : carrier = Set.univ

structure M26StrongDoubleCappedTube (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) extends StrongDoubleCappedTube K t epsilon C where
  tube_epsilon : tube.epsilon = epsilon
  strong_at : ∀ x ∈ tube.carrier, ∃ N : StrongEvolvingNeck K t epsilon,
    N.center = x
  first_cap_connection : cap₁.cap.connection = K.flow.connection t
  second_cap_connection : cap₂.cap.connection = K.flow.connection t
  carrier_eq_univ : carrier = Set.univ

inductive KappaNine88Conclusion
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) : Prop where
  | tube (certificate : M26StrongTube K 0 epsilon)
  | capped (certificate : M26StrongCappedTube K 0 epsilon C)

inductive RepairedKappaNine89Conclusion
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) : Prop where
  | round (roundness :
      ConstantPositiveSectionalCurvature (K.flow.metric 0)
        (K.flow.connection 0))
      (quotient : RoundAncientQuotientCertificate K)
  | compactSmall (certificate : CompactSmallSliceCertificate K C)
  | doubleCapped (tube : M26StrongDoubleCappedTube K 0 epsilon C)

structure RepairedCanonicalNeighborhoodCertificate
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) where
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  compact_alternatives : Nonempty (RepairedKappaNine89Conclusion K epsilon C)

end PoincareConjecture
