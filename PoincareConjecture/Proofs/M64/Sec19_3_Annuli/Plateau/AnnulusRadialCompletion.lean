import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.RadialFlipGeometry









noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture




def m64AnnulusRadialCompletion {M : Type*} (f : LoopPlane → M) (c0 c1 : ℝ → M)
    (p : LoopPlane) : M :=
  if p 1 = 0 then c0 (p 0) else if p 1 = 1 then c1 (p 0) else f p



theorem m64AnnulusRadialCompletion_lower {M : Type*}
    (f : LoopPlane → M) (c0 c1 : ℝ → M) (x : ℝ) :
    m64AnnulusRadialCompletion f c0 c1 (annulusPoint x 0) = c0 x := by
  simp [m64AnnulusRadialCompletion, annulusPoint]



theorem m64AnnulusRadialCompletion_upper {M : Type*}
    (f : LoopPlane → M) (c0 c1 : ℝ → M) (x : ℝ) :
    m64AnnulusRadialCompletion f c0 c1 (annulusPoint x 1) = c1 x := by
  simp [m64AnnulusRadialCompletion, annulusPoint]



theorem m64AnnulusRadialCompletion_interior {M : Type*}
    (f : LoopPlane → M) (c0 c1 : ℝ → M) {p : LoopPlane}
    (hp : p 1 ∈ Ioo (0 : ℝ) 1) :
    m64AnnulusRadialCompletion f c0 c1 p = f p := by
  simp only [m64AnnulusRadialCompletion, if_neg hp.1.ne', if_neg hp.2.ne]




theorem m64AnnulusRadialCompletion_flip {M : Type*}
    (f : LoopPlane → M) (c0 c1 : ℝ → M) :
    m64AnnulusRadialCompletion (f ∘ m64AnnulusRadialFlip) c1 c0 =
      m64AnnulusRadialCompletion f c0 c1 ∘ m64AnnulusRadialFlip := by
  funext p
  have h0 : m64AnnulusRadialFlip p 0 = p 0 := by
    simp [m64AnnulusRadialFlip_apply, m60PlaneReflection_apply, annulusPoint]
  have h1 : m64AnnulusRadialFlip p 1 = 1 - p 1 := by
    simp [m64AnnulusRadialFlip_apply, m60PlaneReflection_apply, annulusPoint, sub_eq_add_neg]
  simp only [Function.comp_apply, m64AnnulusRadialCompletion, h0, h1]
  by_cases hp0 : p 1 = 0
  · simp [hp0]
  by_cases hp1 : p 1 = 1
  · simp [hp1]
  have hn0 : 1 - p 1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hp1)
  have hn1 : 1 - p 1 ≠ 1 := by intro h; exact hp0 (by linarith only [h])
  simp only [if_neg hp0, if_neg hp1, if_neg hn0, if_neg hn1]

end PoincareConjecture
