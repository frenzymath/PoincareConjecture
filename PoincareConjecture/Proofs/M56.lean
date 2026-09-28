import PoincareConjecture.Statements.M56Ancestry
import PoincareConjecture.Proofs.M56.PoincareConstructor

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedFiniteAncestry : RepairedAncestryTheory.{u} := by
  refine { ancestry := ?_, poincare := m56PoincareConstructor }
  intro _G38 G54 _G55 M _ _ _ _ _ _ _ _ _ N D _ F hF W hconn hgroups _ _ _
  exact m56FiniteAncestry G54 (hF ▸ W) hconn hgroups
    (fun H _ => D.certificate.local_finite (Set.Icc 0 H) isCompact_Icc)

end PoincareConjecture
