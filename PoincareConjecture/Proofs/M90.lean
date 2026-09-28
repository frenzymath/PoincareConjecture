import PoincareConjecture.Statements.M90FinalAssembly
import PoincareConjecture.Proofs.M90.Providers









set_option autoImplicit false

universe u

namespace PoincareConjecture



theorem m90FinalAssembly : M90FinalAssemblyStatement.{u} := by
  intro A
  exact ⟨{ smooth := A.smooth, topological := A.topological }⟩









theorem m90FinalAssemblyFromMilestones : M90CompleteAssemblyStatement.{u} := by
  obtain ⟨A⟩ := m90EndpointPackageFromMilestones.{u}
  exact m90FinalAssembly A

end PoincareConjecture
