import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Geometry

/-!
Adapted from Mapher `PoincareMT/Definitions/M26CanonicalNeighborhoods.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M26 repaired canonical-neighborhood certificates

The certificate package records the noncompact alternatives of Corollary 9.88
and the compact-solution alternatives of Theorem 9.89. The stronger all-time
pointwise canonical-neighborhood conclusion is owned by the later
M27/Corollary 9.94 boundary.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]

/-- The source hypothesis excluding an embedded projective plane with trivial
normal bundle. It is attached to the solution carrier so the Corollary 9.88
branch cannot silently be applied to a different manifold. -/
def NoEmbeddedTrivialNormalProjectivePlane
    (_K : AncientKappaSolution 3 M) : Prop :=
  ¬ ∃ f : RealProjectiveTwo × Set.Ioo (-1 : ℝ) 1 → M,
    Topology.IsOpenEmbedding f

/-- Definition 9.82 on the entire slice, with the static tube's epsilon
identified with that of its evolving necks. -/
structure M26StrongTube (K : AncientKappaSolution 3 M) (t epsilon : ℝ)
    extends StrongTubeCertificate K t epsilon where
  tube_epsilon : tube.epsilon = epsilon
  carrier_eq_univ : tube.carrier = Set.univ

/-- A whole-slice capped tube whose tube factor is genuinely strong. -/
structure M26StrongCappedTube (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) extends StrongCappedTube K t epsilon C where
  tube_epsilon : tube.epsilon = epsilon
  strong_at : ∀ x ∈ tube.carrier, ∃ N : StrongEvolvingNeck K t epsilon,
    N.center = x
  cap_connection : cap.cap.connection = K.flow.connection t
  carrier_eq_univ : carrier = Set.univ

/-- Theorem 9.89's whole-slice double-capped strong tube. -/
structure M26StrongDoubleCappedTube (K : AncientKappaSolution 3 M)
    (t epsilon C : ℝ) extends StrongDoubleCappedTube K t epsilon C where
  tube_epsilon : tube.epsilon = epsilon
  strong_at : ∀ x ∈ tube.carrier, ∃ N : StrongEvolvingNeck K t epsilon,
    N.center = x
  first_cap_connection : cap₁.cap.connection = K.flow.connection t
  second_cap_connection : cap₂.cap.connection = K.flow.connection t
  carrier_eq_univ : carrier = Set.univ

/-- The zero-slice alternatives of Corollary 9.88. -/
inductive KappaNine88Conclusion
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) : Prop where
  | tube (certificate : M26StrongTube K 0 epsilon)
  | capped (certificate : M26StrongCappedTube K 0 epsilon C)

/-! The compact alternatives of Theorem 9.89. The round constructor carries
the finite spherical-space-form witness used by M24, so it is not restricted
to the simply connected three-sphere model. -/
inductive RepairedKappaNine89Conclusion
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) : Prop where
  | round (roundness :
      ConstantPositiveSectionalCurvature (K.flow.metric 0)
        (K.flow.connection 0))
      (quotient : RoundAncientQuotientCertificate K)
  | compactSmall (certificate : CompactSmallSliceCertificate K C)
  | doubleCapped (tube : M26StrongDoubleCappedTube K 0 epsilon C)

/-- Quantitative compact-slice output for Theorem 9.89. -/
structure RepairedCanonicalNeighborhoodCertificate
    (K : AncientKappaSolution 3 M) (epsilon C : ℝ) where
  epsilon_pos : 0 < epsilon
  constant_pos : 0 < C
  compact_alternatives : Nonempty (RepairedKappaNine89Conclusion K epsilon C)

end PoincareMT
