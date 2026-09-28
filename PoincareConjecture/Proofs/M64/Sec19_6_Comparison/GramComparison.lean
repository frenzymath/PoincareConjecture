import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AreaEnergy

set_option autoImplicit false

namespace PoincareConjecture

theorem m64_gramDet_add_nonneg
    {b00 b01 b11 s00 s01 s11 : ℝ}
    (hb00 : 0 ≤ b00) (hb11 : 0 ≤ b11) (hs00 : 0 ≤ s00) (hs11 : 0 ≤ s11)
    (hbdet : b01 ^ 2 ≤ b00 * b11)
    (hsdet : s01 ^ 2 ≤ s00 * s11) :
    b00 * b11 - b01 ^ 2 ≤
      (b00 + s00) * (b11 + s11) - (b01 + s01) ^ 2 := by
  have hprod : 0 ≤ (b00 * b11 - b01 ^ 2) * (s00 * s11) :=
    mul_nonneg (sub_nonneg.mpr hbdet) (mul_nonneg hs00 hs11)
  have hsq : 0 ≤ (b00 * s11 - s00 * b11) ^ 2 := sq_nonneg _
  have hsum : 0 ≤ b00 * s11 + s00 * b11 :=
    add_nonneg (mul_nonneg hb00 hs11) (mul_nonneg hs00 hb11)
  have hcross : 2 * b01 * s01 ≤ b00 * s11 + s00 * b11 := by
    nlinarith [hprod, hsq]
  nlinarith

end PoincareConjecture
