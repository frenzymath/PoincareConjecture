import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Geometry
import PoincareLib.Geometry.Riemannian.Surface.Regularity

/-!
# Compact terminal scalar sublevels

Morgan--Tian Claim 11.33, printed p. 288, confines bounded-curvature terminal
sets to compact subsets. The scalar lower bound and properness supplied by
Theorem 11.19 give this directly on the actual terminal slice.

The donor declarations are
`SingularLimitConclusion.isCompact_scalar_sublevel` and
`SingularLimitConclusion.isCompact_closure_of_scalar_bound` in Horizon
`Surgery/Singular/DeepHorn/Geometry/Levels.lean`. We rederive them from the
frozen conclusion and the eligible lower scalar-continuity theorem.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT.M32

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M] [SecondCountableTopology M]
  {F : GeneralizedRicciFlowData.{u}} {T : ℝ}
  {H : SingularTimeAssumptions F T M}

/-- Properness and the lower scalar bound make terminal scalar sublevels
compact, as used in Morgan--Tian Claim 11.33, printed p. 288. -/
theorem terminalScalarSublevel_isCompact (Q : SingularLimitConclusion H) (q : ℝ) :
    IsCompact {x | (Q.extension.extended.connection T).scalarCurvature x ≤ q} := by
  obtain ⟨L, hL⟩ := Q.scalar_lower
  have heq : {x | Q.terminal_scalar x ≤ q} = Q.terminal_scalar ⁻¹' Set.Icc L q := by
    ext x
    exact ⟨fun hx => ⟨hL x, hx⟩, fun hx => hx.2⟩
  rw [← Q.terminal_scalar_eq, heq]
  exact Q.scalar_proper _ isCompact_Icc

/-- A terminal scalar bound gives compact closure on the actual terminal
slice, the compactness conclusion of Claim 11.33, printed p. 288. -/
theorem terminalClosure_isCompact_of_scalarBound (Q : SingularLimitConclusion H)
    (U : Set (Q.extension.extended.slice T).carrier) (q : ℝ)
    (hbound : ∀ x ∈ U, (Q.extension.extended.connection T).scalarCurvature x ≤ q) :
    IsCompact (closure U) := by
  apply (terminalScalarSublevel_isCompact Q q).of_isClosed_subset isClosed_closure
  exact closure_minimal hbound
    (isClosed_le (Q.extension.extended.connection T).continuous_scalarCurvature continuous_const)

end PoincareMT.M32
