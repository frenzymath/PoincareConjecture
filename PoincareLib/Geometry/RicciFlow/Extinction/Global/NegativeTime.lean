import PoincareLib.Geometry.RicciFlow.Extinction.Global.ProfileAlgebra
import PoincareLib.Geometry.RicciFlow.Extinction.Global.InitialWidth

/-!
# A time determined by the fixed initial width

Morgan--Tian Theorem 18.1, printed p. 432, chooses the comparison time from
the initial width before considering a component path reaching that time.
The global certificate places this nonnegative time in the flow domain.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT

variable {g₀ : StandardInitialMetric} {D : RepairedSurgeryFlowData.{u} g₀}
  {W : RepairedEventChildWitness D.flow}
  {ancestry : RepairedFiniteAncestryData D.flow W}

/-- The observation time for the negative-profile argument in Morgan--Tian
Theorem 18.1, p. 432. It depends only on the fixed initial width. -/
noncomputable def m71ExtinctionTime (Q : M71FiniteContinuationService D W ancestry) : ℝ :=
  ((2 + m71InitialWidth Q / (2 * Real.pi)) ^ 4 - 1) / 4

/-- The observation time in Morgan--Tian Theorem 18.1, p. 432, is nonnegative. -/
theorem m71ExtinctionTime_nonneg (Q : M71FiniteContinuationService D W ancestry) :
    0 ≤ m71ExtinctionTime Q :=
  (m71ProfileAlgebra_neg (m71InitialWidth Q) (m71InitialWidth_nonneg Q)).1

/-- The global flow domain contains the chosen observation time, using the
all-time certificate in Morgan--Tian Theorem 15.9, pp. 363-364. -/
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

end PoincareMT
