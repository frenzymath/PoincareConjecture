import PoincareConjecture.Statements.M30ControlledBlowupLimits
import PoincareConjecture.Statements.M30Providers
import PoincareConjecture.Proofs.M30.ContractAssembly
import PoincareConjecture.Proofs.M30.Thm11_1.ShortControlSupplier
import PoincareConjecture.Proofs.M30.Thm11_8.LongControlSupplier

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem m30ControlledGeneralizedBlowupLimits
    (P : M30ControlledBlowupPredecessors.{u}) :
    RepairedControlledBlowupLimitTheory.{u} := by
  let services : M30.M30ContractServices.{u} := {
    mixed := M30.withinFlowJetBoundsService.{0, 0}
    flow := M30.withinBilinearFlowService.{0}
    slice := M30.spatialSliceJetConvergenceService.{0, 0, 0, 0, 0}
    short := M30.shortControlService P.m04
    long := M30.longContractService P }
  exact M30.repairedControlledBlowupLimitTheory_of_services P services

end PoincareConjecture
