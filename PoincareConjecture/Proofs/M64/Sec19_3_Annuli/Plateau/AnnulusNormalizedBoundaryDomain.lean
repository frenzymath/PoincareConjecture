import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.SourceAffineGeometry
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusRadialGeometry










noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareConjecture



theorem m64AnnulusSourceAffine_coordinates (x : ℝ) (s : ℝ) (hs : s ≠ 0) (p : LoopPlane) :
    m64SourceAffine (annulusPoint x 0) s hs p 0 = x + s * p 0 ∧
      m64SourceAffine (annulusPoint x 0) s hs p 1 = s⁻¹ * p 1 := by
  change (annulusPoint x 0 + m64SourceScale s hs p) 0 = _ ∧
    (annulusPoint x 0 + m64SourceScale s hs p) 1 = _
  simp [PiLp.add_apply, annulusPoint, m64SourceScale_apply, m64SourceScaleFactor]



theorem m64AnnulusSourceAffine_face (x : ℝ) (s : ℝ) (hs : s ≠ 0)
    {p : LoopPlane} (hp : p 1 = 0) :
    m64SourceAffine (annulusPoint x 0) s hs p = annulusPoint (x + s * p 0) 0 := by
  obtain ⟨h0, h1⟩ := m64AnnulusSourceAffine_coordinates x s hs p
  ext i
  fin_cases i
  · exact h0
  · simpa [hp, annulusPoint] using h1




theorem m64AnnulusSourceAffine_interior (x : ℝ) {s : ℝ} (hs : 0 < s)
    {p : LoopPlane}
    (hp : m64SourceAffine (annulusPoint x 0) s hs.ne' p ∈ m64AnnulusLowerDomain)
    (hpositive : 0 < p 1) :
    m64SourceAffine (annulusPoint x 0) s hs.ne' p ∈ interior m64AnnulusDomain := by
  apply (m64AnnulusInterior_coordinates _).mpr
  refine ⟨hp.1, hp.2.1, ?_, hp.2.2.2⟩
  rw [(m64AnnulusSourceAffine_coordinates x s hs.ne' p).2]
  exact mul_pos (inv_pos.mpr hs) hpositive



theorem m64SourceAffine_contDiff (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) {k : ℕ∞ω} :
    ContDiff ℝ k (m64SourceAffine a s hs) :=
  contDiff_const.add (m64SourceScale s hs).contDiff

end PoincareConjecture
