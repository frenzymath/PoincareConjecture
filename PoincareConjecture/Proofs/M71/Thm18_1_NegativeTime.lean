import PoincareConjecture.Proofs.M71.Thm18_1_ProfileAlgebra
import PoincareConjecture.Proofs.M71.Thm18_1_InitialWidth

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}

noncomputable def m71ExtinctionTime (Q : M71FiniteContinuationService D W ancestry) : ℝ :=
  ((2 + m71InitialWidth Q / (2 * Real.pi)) ^ 4 - 1) / 4

theorem m71ExtinctionTime_nonneg (Q : M71FiniteContinuationService D W ancestry) :
    0 ≤ m71ExtinctionTime Q :=
  (m71ProfileAlgebra_neg (m71InitialWidth Q) (m71InitialWidth_nonneg Q)).1

theorem m71ExtinctionTime_mem
    {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [IsManifold (𝓡 3) ∞ M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [CompactSpace M]
    {N : NormalizedInitialMetric (M := M)} {G : RepairedGlobalFlowData N}
    (input : M71GlobalExtinctionInput N G) :
    m71ExtinctionTime input.continuation ∈ input.D.flow.time_domain := by
  rw [input.flow_eq, G.certificate.time_domain_eq]
  exact m71ExtinctionTime_nonneg input.continuation

end PoincareConjecture
