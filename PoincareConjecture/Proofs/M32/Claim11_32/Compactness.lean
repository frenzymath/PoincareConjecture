import PoincareConjecture.Definitions.Ch11.SingularLimits
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Regularity

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions F T M}

theorem terminalScalarSublevel_isCompact (Q : SingularLimitConclusion H) (q : ℝ) :
    IsCompact {x | (Q.extension.extended.connection T).scalarCurvature x ≤ q} := by
  obtain ⟨L, hL⟩ := Q.scalar_lower
  have heq : {x | Q.terminal_scalar x ≤ q} = Q.terminal_scalar ⁻¹' Set.Icc L q := by
    ext x
    exact ⟨fun hx => ⟨hL x, hx⟩, fun hx => hx.2⟩
  rw [← Q.terminal_scalar_eq, heq]
  exact Q.scalar_proper _ isCompact_Icc

theorem terminalClosure_isCompact_of_scalarBound (Q : SingularLimitConclusion H)
    (U : Set (Q.extension.extended.slice T).carrier) (q : ℝ)
    (hbound : ∀ x ∈ U, (Q.extension.extended.connection T).scalarCurvature x ≤ q) :
    IsCompact (closure U) := by
  apply (terminalScalarSublevel_isCompact Q q).of_isClosed_subset isClosed_closure
  exact closure_minimal hbound
    (isClosed_le (Q.extension.extended.connection T).continuous_scalarCurvature continuous_const)

end PoincareConjecture.M32
