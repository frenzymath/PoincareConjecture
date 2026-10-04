import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Source.AffineGeometry
import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.RadialGeometry

/-! The actual normalized upper half disk lies in the original annulus,
and its flat face retains the original physical boundary parameter.
Source: Morrey boundary coordinates; M64 regular-curve-boundary-c1
derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareMT

/-- Literal tangential and normal coordinates of the centered source map. Proof expansion
for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSourceAffine_coordinates (x : ℝ) (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) :
    m64SourceAffine (annulusPoint x 0) s hs p 0 = x + s * p 0 ∧
      m64SourceAffine (annulusPoint x 0) s hs p 1 = s⁻¹ * p 1 := by
  change (annulusPoint x 0 + m64SourceScale s hs p) 0 = _ ∧
    (annulusPoint x 0 + m64SourceScale s hs p) 1 = _
  simp [PiLp.add_apply, annulusPoint, m64SourceScale_apply, m64SourceScaleFactor]

/-- The normalized flat face is the original face with its actual tangential affine
parameter. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64AnnulusSourceAffine_face (x : ℝ) (s : ℝ) (hs : s ≠ 0)
    {p : LoopPlane} (hp : p 1 = 0) :
    m64SourceAffine (annulusPoint x 0) s hs p = annulusPoint (x + s * p 0) 0 := by
  obtain ⟨h0, h1⟩ := m64AnnulusSourceAffine_coordinates x s hs p
  ext i
  fin_cases i
  · exact h0
  · simpa [hp, annulusPoint] using h1

/-- Positive source modulus preserves the interior side of the lower face inside the
original reflected neighborhood. Proof expansion for Morgan-Tian (2007), Lemma 19.15, pp.
447-449. -/
theorem m64AnnulusSourceAffine_interior (x : ℝ) {s : ℝ} (hs : 0 < s)
    {p : LoopPlane}
    (hp : m64SourceAffine (annulusPoint x 0) s hs.ne' p ∈ m64AnnulusLowerDomain)
    (hpositive : 0 < p 1) :
    m64SourceAffine (annulusPoint x 0) s hs.ne' p ∈ interior m64AnnulusDomain := by
  apply (m64AnnulusInterior_coordinates _).mpr
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  rw [(m64AnnulusSourceAffine_coordinates x s hs.ne' p).2]
  exact mul_pos (inv_pos.mpr hs) hpositive

/-- The genuine affine normalization is smooth at every finite or infinite order. Proof
expansion for Morgan-Tian (2007), Lemma 19.15, pp. 447-449. -/
theorem m64SourceAffine_contDiff (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) {k : ℕ∞ω} :
    ContDiff ℝ k (m64SourceAffine a s hs) :=
  contDiff_const.add (m64SourceScale s hs).contDiff

end PoincareMT
