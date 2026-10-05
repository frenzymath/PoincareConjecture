import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Geometry

/-!
# Blow-up sequences in one actual generalized flow

The flow and selected points are retained literally. Positivity and
divergence are the scalar statements for those same points.
Source: Morgan-Tian Theorem 12.28, pp. 323-324; bad-point selection
derivation, section 4.
-/

set_option autoImplicit false

open Filter

universe u

namespace PoincareMT.M34

/-- The frozen blow-up sequence associated to diverging positive scalar
values in one fixed actual generalized flow (Theorem 12.28). -/
def fixedFlowBlowupSequence (G : GeneralizedRicciFlowData.{u}) (p : ℕ → G.point)
    (hpositive : ∀ k, 0 < G.scalar (p k))
    (hdiverges : Tendsto (fun k => G.scalar (p k)) atTop atTop) :
    GeneralizedBlowupSequence.{u} where
  flow := fun _ => G
  base := p
  base_scalar_pos := hpositive
  scalar_diverges := hdiverges

end PoincareMT.M34
