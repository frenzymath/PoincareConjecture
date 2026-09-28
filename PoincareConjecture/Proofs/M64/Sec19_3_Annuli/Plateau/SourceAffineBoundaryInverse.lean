import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusNormalizedBoundaryDomain









noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set
open scoped ContDiff

namespace PoincareConjecture



theorem m64SourceAffine_zero (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    m64SourceAffine a s hs 0 = a := by
  change a + m64SourceScale s hs 0 = a
  rw [map_zero, add_zero]



theorem m64SourceAffine_symm_center (a : LoopPlane) (s : ℝ) (hs : s ≠ 0) :
    (m64SourceAffine a s hs).symm a = 0 := by
  calc
    _ = (m64SourceAffine a s hs).symm (m64SourceAffine a s hs 0) :=
      congrArg (m64SourceAffine a s hs).symm (m64SourceAffine_zero a s hs).symm
    _ = 0 := (m64SourceAffine a s hs).symm_apply_apply 0




theorem m64SourceAffine_symm_contDiff (a : LoopPlane) (s : ℝ) (hs : s ≠ 0)
    {k : ℕ∞ω} : ContDiff ℝ k (m64SourceAffine a s hs).symm := by
  change ContDiff ℝ k (fun p => (m64SourceScale s hs).symm (-a + p))
  exact (m64SourceScale s hs).symm.contDiff.comp (contDiff_const.add contDiff_id)




theorem m64AnnulusSourceAffine_symm_normal (x s : ℝ) (hs : s ≠ 0) (p : LoopPlane) :
    (m64SourceAffine (annulusPoint x 0) s hs).symm p 1 = s * p 1 := by
  change (m64SourceScale s hs).symm (-annulusPoint x 0 + p) 1 = _
  simp [m64SourceScale_symm_apply, m64SourceScaleFactor, annulusPoint]




theorem m64AnnulusSourceAffine_symm_halfPlane (x : ℝ) {s : ℝ} (hs : 0 < s) :
    MapsTo (m64SourceAffine (annulusPoint x 0) s hs.ne').symm
      {p : LoopPlane | 0 ≤ p 1} {p : LoopPlane | 0 ≤ p 1} := by
  intro p hp
  change 0 ≤ (m64SourceAffine (annulusPoint x 0) s hs.ne').symm p 1
  rw [m64AnnulusSourceAffine_symm_normal]
  exact mul_nonneg hs.le hp

end PoincareConjecture
