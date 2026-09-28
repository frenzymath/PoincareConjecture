import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

set_option autoImplicit false

open Set Affine

namespace AffineIndependent

variable {𝕜 E P : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AffineSpace E P] [FiniteDimensional 𝕜 E] {s : Finset P}

noncomputable def affineBasisOfCard (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) : AffineBasis s 𝕜 P where
  toFun := Subtype.val
  ind' := hs
  tot' := hs.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simpa using hcard)

@[simp] theorem affineBasisOfCard_apply (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) (i : s) :
    hs.affineBasisOfCard hcard i = (i : P) := rfl

@[simp] theorem range_affineBasisOfCard (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) :
    range (hs.affineBasisOfCard hcard) = (s : Set P) := Subtype.range_coe

end AffineIndependent
