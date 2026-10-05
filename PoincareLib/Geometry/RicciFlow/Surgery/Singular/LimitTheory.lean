import PoincareLib.Geometry.RicciFlow.Surgery.Singular.Limit
import PoincareLib.Topology.Manifold.NeckCap.Theory

/-!
Adapted from Mapher `PoincareMT/Statements/M31SingularRegularLimit.lean` at
`0bf00434d6783c9fed79b6a8fa3a8349cfc78335`. Declaration bodies are retained;
see `references/ricci-flow/mapher/terminal-accuracy-contract.json`.
-/

/-!
# M31 repaired singular-time regular-limit statement

Given the Appendix A theory, choose a positive epsilon threshold below its
threshold divided by `terminalAccuracyFactor` and small enough for
Proposition 2.19. For every generalized
flow and finite singular time satisfying Assumptions 11.18 with epsilon below
that chosen threshold, construct the complete regular-limit certificate.
The chosen bound precedes the reference manifold, flow and terminal time,
so it remains valid when surgery changes the manifold. A bare numeric cap
ceiling does not replace this source calibration.

Source: Morgan--Tian, Chapter 11 opening, printed p. 267; Theorem 11.19 and
Lemma 11.28, printed pp. 279--287. The printed conclusion uses doubled
epsilon; the formal conclusion uses `terminalAccuracyFactor * epsilon`, since
the cap case of Proposition 9.79(3) does not deliver a factor two (revision of
2026-09-22, see `terminalAccuracyFactor`).
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareMT

structure RepairedSingularRegularLimitTheory : Prop where
  limit : ∀ A : RepairedNeckCapTopologyTheory.{u},
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ terminalAccuracyFactor * epsilon₀ ≤ A.epsilon₀ ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] [SecondCountableTopology M]
        {F : GeneralizedRicciFlowData.{u}} {T : ℝ},
        ∀ H : SingularTimeAssumptions F T M,
          H.epsilon ≤ epsilon₀ →
            Nonempty (RepairedSingularRegularLimitData H)

end PoincareMT
