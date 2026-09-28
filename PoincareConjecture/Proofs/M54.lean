import PoincareConjecture.Statements.M54GroupEffects
import PoincareConjecture.Proofs.M54.Persistence
import PoincareConjecture.Proofs.M54.ConnectedSum.Reconstruction

set_option autoImplicit false

universe u

namespace PoincareConjecture

theorem repairedGroupEffects : RepairedGroupEffectsTheory.{u} := by
  exact ⟨repairedSurgeryGroupEffects, repairedGroupPersistence⟩

end PoincareConjecture
