import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Maps.SourcePhaseSets

set_option autoImplicit false
open Set

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "L" => hamiltonLowerPeriodLattice (Fin 2)
local notation "X" => LatticeHandleAmbient (Fin 1) (Fin 2) L
local notation "H" => LatticeHandle (Fin 1) (Fin 2) L
local notation "p" => (4 * (128 : ℝ))

theorem phaseArc_add_period (a b : ℝ) :
    AddCircle.closedIntervalArc p (a + p) (b + p) = AddCircle.closedIntervalArc p a b := by
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨t - p, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
    change ((t - p : ℝ) : AddCircle p) = z
    rw [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    exact htz
  · rintro ⟨t, ht, htz⟩
    exact ⟨t + p, ⟨by linarith [ht.1], by linarith [ht.2]⟩,
      (AddCircle.coe_add_period p t).trans htz⟩

theorem sourceSlab_add_period (phi : C(H, H)) (a b : ℝ) :
    sourceSlab phi (a + p) (b + p) = sourceSlab phi a b := by
  rw [sourceSlab_eq_inter_phase, sourceSlab_eq_inter_phase, phaseArc_add_period]

end PoincareConjecture.M76.HamiltonIntervalTorus
