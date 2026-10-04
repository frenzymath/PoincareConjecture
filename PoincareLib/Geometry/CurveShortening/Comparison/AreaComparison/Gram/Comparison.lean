import PoincareLib.Geometry.CurveShortening.Comparison.Annulus
import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy

/-!
# Two-column Gram comparison for the circle-product projection

The vertical circle columns add a positive-semidefinite Gram matrix.  The
algebraic two-column form is kept independent of the manifold differential so
that the geometric projection proof can use it pointwise at differentiability
points.

Morgan--Tian context: Section 19.6, Lemmas 19.30-19.31, printed pp. 461-466.
-/

set_option autoImplicit false

namespace PoincareMT

/-! Adding a positive-semidefinite two-column Gram matrix cannot decrease the
two-dimensional Gram determinant. -/
/-- Adding a positive semidefinite two-by-two Gram matrix cannot decrease its determinant.
Source: Auxiliary step for MT Lemma 19.30, p. 462; the actual half-disk collar in
`proof-work/tasks/M64/reports/2026-09-24-sharp-polar-collar.md`. -/
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

end PoincareMT
