import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.HalfTurnOverlap

/-! Filling the two angular edges from the second continuous annular
chart. Every radially closed open-angle value is retained. Source:
Lemaire 1982, p. 102; M64 two-cut assembly derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareMT

local notation "v" => annulusPoint (curvePeriod / 2) 0

/-- Use the second chart only on the two original angular cut lines. Source: MT Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-26-two-cut-c1-assembly.md`. -/
def m64AnnulusCutCompletion {M : Type*} (f g : LoopPlane → M) (p : LoopPlane) : M :=
  if p 0 = 0 then g (p + v) else if p 0 = curvePeriod then g (p - v) else f p

/-- All original values away from the two cut lines are unchanged. Source: MT Lemma 19.15,
pp. 447-449; M64 derivation `2026-09-26-two-cut-c1-assembly.md`. -/
theorem m64AnnulusCutCompletion_interior {M : Type*} (f g : LoopPlane → M)
    {p : LoopPlane} (hp : p 0 ∈ Ioo (0 : ℝ) curvePeriod) :
    m64AnnulusCutCompletion f g p = f p := by
  simp only [m64AnnulusCutCompletion, if_neg hp.1.ne', if_neg hp.2.ne]

/-- Both angular edges read the same point in the second chart. Source: MT Lemma 19.15, pp.
447-449; M64 derivation `2026-09-26-two-cut-c1-assembly.md`. -/
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

end PoincareMT
