import PoincareConjecture.Definitions.Ch11.BlowupLimits

set_option autoImplicit false

open Filter

universe u

namespace PoincareConjecture.M34

def fixedFlowBlowupSequence (G : GeneralizedRicciFlowData.{u}) (p : ℕ → G.point)
    (hpositive : ∀ k, 0 < G.scalar (p k))
    (hdiverges : Tendsto (fun k => G.scalar (p k)) atTop atTop) :
    GeneralizedBlowupSequence.{u} where
  flow := fun _ => G
  base := p
  base_scalar_pos := hpositive
  scalar_diverges := hdiverges

end PoincareConjecture.M34
