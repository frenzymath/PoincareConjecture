import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Collars.Mathlib.CollarCollapseCarrierPL

/-!
# Fixed-sign phase formulas for the collar collapse

On either finite phase subcomplex the sign is a constant (`1` or
`-1`). Scaling the scalar displacement by that constant preserves the
same finite carrier. These are fixed-time endpoint formulas and do not
assert a global phase lift or joint piecewise affinity in homotopy time.
See rigidity056, sections 2 and 7.
-/

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Scaling the spatial collar displacement by one fixed phase value
preserves finite piecewise affinity on the complete source carrier. -/
theorem finitePiecewiseAffineOn_scaled_displacement {t : E → ℝ}
    {S : Set E} (ht : FinitePiecewiseAffineOn t S) (r ε : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => ε * displacement r (t x)) S := by
  have hd := finitePiecewiseAffineOn_displacement ht r
  exact (hd.postcomp (ε • ContinuousAffineMap.id ℝ ℝ)).congr
    (fun _ _ => rfl)

/-- A fixed-sign target displacement paired with an existing finite PL
map retains the whole phase carrier. -/
theorem finitePiecewiseAffineOn_phase_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r ε : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => (u x, ε * displacement r (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_scaled_displacement ht r ε)

end CollarCollapse
