import PoincareConjecture.Statements.M37SurgeryFlow









set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture
















theorem repairedSurgeryFlow : RepairedSurgeryFlowTheory.{u} := by
  refine ⟨?_⟩
  intro S B F compatibility
  exact ⟨{
    data := compatibility.data.toRepairedSurgeryFlowData
    flow_eq := compatibility.flow_eq
    compatibility_data := compatibility.data
    core_eq := rfl
    metric_surgery_source := compatibility.metric_surgery_source
    branch_application := compatibility.branch_application
  }⟩

end PoincareConjecture
