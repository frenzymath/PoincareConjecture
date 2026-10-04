import PoincareLib.Geometry.Riemannian.Curvature.Calculus
import PoincareLib.Geometry.Riemannian.ScalarOperators
import PoincareLib.Geometry.RicciFlow.Basic

/-!
Adapted from Mapher `PoincareMT/Statements/M47ScalarPersistence.lean` at
`f927d9e1f0810042766d3b5f64d3f4da02ee93cc`. Declaration bodies are retained;
see `references/ricci-flow/mapher/surgery-adapters-port.json`.
-/

/-!
# M47 local scalar persistence support

The conclusion uses only the actual flow, initial metric ball and curvature
bounds. M04 services are separate proof inputs. The cutoff and local comparison
argument belong to M47's existing admission, not to the surgery hypotheses.

Sources: Morgan--Tian equation (3.7), p. 41, and the local-cover/cutoff argument
on pp. 52--54. Keep the full-slab correction MT-SHI-CUTOFF-SPACETIME.
See reviews/contracts/2026-09-15-m47-scalar-persistence-round1.md.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

/-- The three actual M04 services used by the local comparison argument. -/
structure M47ScalarPersistencePredecessors : Prop where
  tensor_calculus :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (g : RiemannianMetric 3 M) (D : LeviCivitaData g), D.CurvatureTensorCalculus
  scalar_regular :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J),
      ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓘(ℝ, ℝ)) ∞
        (fun p : ℝ × M ↦ (F.connection p.1).scalarCurvature p.2) (J ×ˢ Set.univ)
  scalar_evolution :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      (J : Set ℝ) (F : RicciFlow 3 M J) (t : ℝ), t ∈ J → ∀ x : M,
      HasDerivWithinAt (fun s ↦ (F.connection s).scalarCurvature x)
        ((F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x) J t

/-- A positive scalar patch persists at its center for a uniform short time.
The initial bound is on the whole ball; both spacetime bounds use that same
fixed initial ball. The duration is chosen before the manifold and flow. -/
def M47LocalScalarPersistenceStatement : Prop :=
  ∀ K a : ℝ, 0 < K → 0 < a →
    ∃ tau : ℝ, 0 < tau ∧ tau ≤ 1 ∧
      ∀ (M : Type u) [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [T2Space M] [SecondCountableTopology M],
      ∀ T : ℝ, 0 < T →
      ∀ (F : RicciFlow 3 M (Set.Icc 0 T)) (p : M),
        IsCompact (closure ((F.metric 0).ball p a)) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p a,
          (F.connection t).curvatureTensorNorm x ≤ K) →
        (∀ t ∈ Set.Icc 0 T, ∀ x ∈ (F.metric 0).ball p a,
          -1 ≤ (F.connection t).scalarCurvature x) →
        (∀ x ∈ (F.metric 0).ball p a,
          3 / 4 ≤ (F.connection 0).scalarCurvature x) →
        ∀ t ∈ Set.Icc 0 (min T tau), 1 / 4 ≤ (F.connection t).scalarCurvature p

end PoincareMT
