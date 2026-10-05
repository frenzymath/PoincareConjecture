import PoincareLib.Geometry.RicciFlow.Surgery.Induction.Noncollapse.Attainment.Gauge.GaugeRecoverySequence
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Paths.Action.LLength

/-!
# The literal action infimum bounds every weak recovery

Proposition 16.4 and Claim 16.25, pp. 369 and 389-390. Admissible recovery
compares the finite weak action directly with the original M14 infimum.
No ordinary-flow attainment theorem is used.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareMT.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

/-- The original actual path infimum is below the action of every
finite weak gauge primitive with the same endpoints and clock.
Source: the direct method in Proposition 16.4, p. 369. -/
theorem actionValue_le_gauge_primitive (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau))) :
    M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) ≤ R.action := by
  obtain ⟨p, hp⟩ := gauge_primitive_recovery_sequence hM12 htau gamma hgamma hclock R
  exact ge_of_tendsto hp (Eventually.of_forall (fun k => M14.actionValue_le_action hfinite (p k)))

/-- A weak limit below the original infimum therefore has exactly
that infimum as its action. This is weak minimality, not yet regularity
or admissible attainment. Source: Proposition 16.4, p. 369. -/
theorem gauge_primitive_action_eq_value (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hmin : R.action ≤ M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau))) :
    R.action = M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) :=
  le_antisymm hmin (actionValue_le_gauge_primitive hM12 htau gamma hgamma hclock R hfinite)

end PoincareMT.Proofs.M46
