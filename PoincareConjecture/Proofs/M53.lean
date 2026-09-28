import PoincareConjecture.Statements.M53SphereSeparation
import PoincareConjecture.Proofs.M53.Prop15_12_Complement
import PoincareConjecture.Proofs.M53.Prop15_12_Separation

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedSphereSeparation : RepairedSphereSeparationTheory.{u} := by
  refine ⟨?_⟩
  intro M _ _ _ _ _ _ _
  refine ⟨⟨?_⟩⟩
  intro S
  refine ⟨Proofs.M53.sphere_complement_nonempty S, ?_⟩
  intro hconn
  apply Proofs.M53.sphere_complement_not_isPreconnected S
  simpa only [Set.compl_eq_univ_sdiff] using hconn.isPreconnected

end PoincareConjecture
