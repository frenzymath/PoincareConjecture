import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapsePL
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapseHomotopy

/-!
# Finite PL carrier formulas for the collar collapse

The scalar collapse can be paired with an existing finite PL map on
the same complete carrier. These are fixed-time endpoint formulas;
they make no joint piecewise-affine claim in the homotopy parameter.
See rigidity056, sections 2 and 7.
-/

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A fixed-time scalar collar motion is finite PL on the original
carrier whenever its source coordinate is. See rigidity056, section 7. -/
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

/-- Pairing an existing finite PL map with the collapsed source
height preserves the complete source carrier. -/
theorem finitePiecewiseAffineOn_collapse_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => (u x, height r (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_height ht r)

/-- Pairing an existing finite PL map with a fixed-time source motion
preserves the complete source carrier. -/
theorem finitePiecewiseAffineOn_move_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r s : ℝ) :
    FinitePiecewiseAffineOn (fun x => (u x, move r s (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_move ht r s)

end CollarCollapse
