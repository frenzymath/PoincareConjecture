import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Affine bases supplied by full-dimensional finite simplices

An independent finite set of the ambient dimension plus one is an
affine basis, retaining its original vertex labels. See Cairns 1940,
pp. 804--806 and M76 derivation 69.
-/

set_option autoImplicit false

open Set Affine

namespace AffineIndependent

variable {𝕜 E P : Type*} [DivisionRing 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [AffineSpace E P] [FiniteDimensional 𝕜 E] {s : Finset P}

/-- A full-dimensional independent finite set gives an affine
basis indexed by its original vertices. See Cairns pp. 804--806
and M76 derivation 69. -/
noncomputable def affineBasisOfCard (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) : AffineBasis s 𝕜 P where
  toFun := Subtype.val
  ind' := hs
  tot' := hs.affineSpan_eq_top_iff_card_eq_finrank_add_one.mpr (by simpa using hcard)

/-- The full-simplex basis uses the original point of each
vertex subtype. See Cairns pp. 804--806 and M76 derivation 69. -/
@[simp] theorem affineBasisOfCard_apply (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) (i : s) :
    hs.affineBasisOfCard hcard i = (i : P) := rfl

/-- The range of the full-simplex basis is the original finite
vertex set. See Cairns pp. 804--806 and M76 derivation 69. -/
@[simp] theorem range_affineBasisOfCard (hs : AffineIndependent 𝕜 ((↑) : s → P))
    (hcard : s.card = Module.finrank 𝕜 E + 1) :
    range (hs.affineBasisOfCard hcard) = (s : Set P) := Subtype.range_coe

end AffineIndependent
