import PoincareConjecture.Statements.M44CapPersistence
import PoincareConjecture.Proofs.M44.Scales
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Prop16_5_Assembly




































set_option autoImplicit false

universe u

namespace PoincareConjecture



theorem repairedCapPersistence
    (P : M44CapPersistencePredecessors.{u}) :
    RepairedCapPersistenceTheory.{u} :=
  ⟨M44.exists_repaired_cap_persistence_data P⟩

end PoincareConjecture
