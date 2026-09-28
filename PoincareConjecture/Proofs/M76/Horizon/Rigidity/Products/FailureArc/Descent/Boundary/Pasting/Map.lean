import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.SourceCopies



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn.AnnulusSquareCopies

def map {X Y : Type*} {f : Fin 2 → (ℝ × ℝ) → X} {g : (ℝ × ℝ) → X}
    (C : AnnulusSquareCopies f g) (p : X → Y) :
    AnnulusSquareCopies (fun j ↦ p ∘ f j) (p ∘ g) where
  piece := C.piece
  chart := C.chart
  finitePL := C.finitePL
  cover := C.cover
  val := fun j z ↦ congrArg p (C.val j z)
  cross := C.cross
  outer := C.outer
  inner := C.inner

end PoincareConjecture.M76.Dehn.AnnulusSquareCopies
