import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.SmallRadiusAssembly
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.HalfRadiusHistory
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.PositiveAncestor

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace PoincareConjecture.Proofs.M46

theorem regularSourceProducer_of_reviewed_producers (P : M46Predecessors.{u})
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {taubar l0 V rNext cutoff rho A eta theta : ℝ}
    (stable : StableSourceProducer.{u} p taubar l0 V)
    (avoid : CapAvoidanceProducer.{u} p rNext cutoff rho A eta theta)
    (minimize : MinimizingRegionProducer.{u} p rNext cutoff rho)
    (caps : ∀ (F : SurgeryFlowData.{u}) (O : SurgeryObservation F)
      (inputs : ObservedInputs p rNext cutoff F O),
      OverlapCapControl p O inputs.old A eta theta) :
    RegularSourceProducer.{u} p rNext cutoff rho taubar l0 V := by
  intro F O inputs D hnew _hscalar hlarge
  obtain ⟨H⟩ := halfRadiusHistory P D
  obtain ⟨C, budget⟩ := avoid F O inputs D H hnew hlarge (caps F O inputs)
  obtain ⟨region⟩ := minimize F O inputs D H hnew hlarge C budget
  exact ⟨H, stable rNext cutoff F O inputs D H hnew C budget region
    (positiveAncestorExclusion H)⟩

end PoincareConjecture.Proofs.M46
