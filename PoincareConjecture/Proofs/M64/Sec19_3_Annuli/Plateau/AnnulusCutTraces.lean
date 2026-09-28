import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusCutCompletion

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set

namespace PoincareConjecture

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

end PoincareConjecture
