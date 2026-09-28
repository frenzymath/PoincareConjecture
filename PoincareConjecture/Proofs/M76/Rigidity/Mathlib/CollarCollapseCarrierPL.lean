import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapsePL
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapseHomotopy

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finitePiecewiseAffineOn_move {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r s : ℝ) :
    FinitePiecewiseAffineOn (fun x => move r s (t x)) S := by
  have hd := finitePiecewiseAffineOn_displacement ht r
  have hs : FinitePiecewiseAffineOn
      (fun x => s * displacement r (t x)) S := by
    exact (hd.postcomp (s • ContinuousAffineMap.id ℝ ℝ)).congr
      (fun _ _ => rfl)
  change FinitePiecewiseAffineOn
    (fun x => t x - s * displacement r (t x)) S
  exact ht.sub hs

theorem finitePiecewiseAffineOn_collapse_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => (u x, height r (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_height ht r)

theorem finitePiecewiseAffineOn_move_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r s : ℝ) :
    FinitePiecewiseAffineOn (fun x => (u x, move r s (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_move ht r s)

end CollarCollapse
