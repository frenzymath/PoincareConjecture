import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusHalfTurnOverlap









noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture

local notation "v" => annulusPoint (curvePeriod / 2) 0



def m64AnnulusCutCompletion {M : Type*} (f g : LoopPlane → M) (p : LoopPlane) : M :=
  if p 0 = 0 then g (p + v) else if p 0 = curvePeriod then g (p - v) else f p



theorem m64AnnulusCutCompletion_interior {M : Type*} (f g : LoopPlane → M)
    {p : LoopPlane} (hp : p 0 ∈ Ioo (0 : ℝ) curvePeriod) :
    m64AnnulusCutCompletion f g p = f p := by
  simp only [m64AnnulusCutCompletion, if_neg hp.1.ne', if_neg hp.2.ne]



theorem m64AnnulusCutCompletion_edges {M : Type*} (f g : LoopPlane → M) (y : ℝ) :
    m64AnnulusCutCompletion f g (annulusPoint 0 y) =
        g (annulusPoint (curvePeriod / 2) y) ∧
      m64AnnulusCutCompletion f g (annulusPoint curvePeriod y) =
        g (annulusPoint (curvePeriod / 2) y) := by
  have hP : curvePeriod ≠ 0 := by unfold curvePeriod; positivity
  have hleft : annulusPoint 0 y + v = annulusPoint (curvePeriod / 2) y := by
    ext i; fin_cases i <;> simp [annulusPoint]
  have hright : annulusPoint curvePeriod y - v = annulusPoint (curvePeriod / 2) y := by
    ext i; fin_cases i <;> simp [annulusPoint]; ring
  simp only [m64AnnulusCutCompletion, annulusPoint, Matrix.cons_val_zero, if_neg hP]
  exact ⟨congrArg g hleft, congrArg g hright⟩

end PoincareConjecture
