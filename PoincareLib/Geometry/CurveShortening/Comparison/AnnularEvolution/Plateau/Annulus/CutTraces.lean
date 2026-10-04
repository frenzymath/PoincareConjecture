import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Plateau.Annulus.CutCompletion

/-! Literal radial traces survive angular-cut completion. The shifted
second-chart trace and the original periodicity identify the corners.
Source: Lemaire 1982, p. 102; M64 two-cut assembly derivation.

Morgan--Tian context: Lemma 19.15 and its annular area-to-energy construction, printed pp.
447-449.
-/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareMT

/-- Original periodic trace data and their half-period translate give the exact trace of the
completed map, including both angular endpoints. Source: MT Lemma 19.15, pp. 447-449; M64
derivation `2026-09-26-two-cut-c1-assembly.md`. -/
theorem m64AnnulusCutCompletion_trace {M : Type*} (f g : LoopPlane → M)
    (c : ℝ → M) (hc : Function.Periodic c curvePeriod) (y : ℝ)
    (hf : ∀ x : ℝ, f (annulusPoint x y) = c x)
    (hg : ∀ x : ℝ, g (annulusPoint x y) = c (x + curvePeriod / 2)) :
    ∀ x ∈ Icc (0 : ℝ) curvePeriod,
      m64AnnulusCutCompletion f g (annulusPoint x y) = c x := by
  intro x hx
  have hh : curvePeriod / 2 + curvePeriod / 2 = curvePeriod := by ring
  by_cases hx0 : x = 0
  · subst x
    rw [(m64AnnulusCutCompletion_edges f g y).1, hg, hh]
    simpa only [zero_add] using hc 0
  by_cases hxP : x = curvePeriod
  · subst x
    rw [(m64AnnulusCutCompletion_edges f g y).2, hg, hh]
  · have hxi : (annulusPoint x y) 0 ∈ Ioo (0 : ℝ) curvePeriod :=
      ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxP⟩
    rw [m64AnnulusCutCompletion_interior f g hxi, hf]

end PoincareMT
