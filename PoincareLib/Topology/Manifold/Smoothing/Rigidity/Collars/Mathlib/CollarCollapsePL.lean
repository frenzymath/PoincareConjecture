import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapse

/-!
# Finite PL formulas for the spatial collar collapse

The fixed-width scalar formulas use affine combinations, minima
and maxima on the original finite carrier. No assertion of joint
piecewise affinity in homotopy time is made. See Hudson1969
pp.15--19 and rigidity056, section7.
-/

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- Clipping a finite PL scalar coordinate preserves its entire
finite carrier. See rigidity056, section7. -/
theorem finitePiecewiseAffineOn_clip {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => clip r (t x)) S := by
  have hconst (a : ℝ) : FinitePiecewiseAffineOn (fun _ : E => a) S :=
    (ht.postcomp (ContinuousAffineMap.const ℝ ℝ a)).congr (fun _ _ => rfl)
  exact (hconst (-r)).max (ht.min (hconst r))

/-- The endpoint source collapse is finite PL on the same full
carrier as its original scalar coordinate. See rigidity056, section7. -/
theorem finitePiecewiseAffineOn_height {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => height r (t x)) S := by
  have hc := finitePiecewiseAffineOn_clip ht r
  have hc2 := finitePiecewiseAffineOn_clip ht (2 * r)
  have htwice : FinitePiecewiseAffineOn (fun x => 2 * clip r (t x)) S :=
    (hc.postcomp ((2 : ℝ) • ContinuousAffineMap.id ℝ ℝ)).congr (fun _ _ => rfl)
  exact (ht.sub htwice).add hc2

/-- The spatial target displacement is finite PL on the same
full carrier. See rigidity056, section7. -/
theorem finitePiecewiseAffineOn_displacement {t : E → ℝ} {S : Set E}
    (ht : FinitePiecewiseAffineOn t S) (r : ℝ) :
    FinitePiecewiseAffineOn (fun x => displacement r (t x)) S :=
  ht.sub (finitePiecewiseAffineOn_height ht r)

end CollarCollapse
