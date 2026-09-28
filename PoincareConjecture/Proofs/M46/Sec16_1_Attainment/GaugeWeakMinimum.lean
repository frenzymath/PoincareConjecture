import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoverySequence
import PoincareConjecture.Proofs.M14.Sec6_1_LLength

set_option autoImplicit false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}

theorem actionValue_le_gauge_primitive (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau))) :
    M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) ≤ R.action := by
  obtain ⟨p, hp⟩ := gauge_primitive_recovery_sequence hM12 htau gamma hgamma hclock R
  exact ge_of_tendsto hp (Eventually.of_forall (fun k => M14.actionValue_le_action hfinite (p k)))

theorem gauge_primitive_action_eq_value (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hmin : R.action ≤ M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau))) :
    R.action = M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)) :=
  le_antisymm hmin (actionValue_le_gauge_primitive hM12 htau gamma hgamma hclock R hfinite)

end PoincareConjecture.Proofs.M46
