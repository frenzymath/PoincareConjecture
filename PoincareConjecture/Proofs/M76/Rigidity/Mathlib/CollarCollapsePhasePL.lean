import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.CollarCollapseCarrierPL

set_option autoImplicit false

open Set Geometry

namespace CollarCollapse

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem finitePiecewiseAffineOn_scaled_displacement {t : E → ℝ}
    {S : Set E} (ht : FinitePiecewiseAffineOn t S) (r ε : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => ε * displacement r (t x)) S := by
  have hd := finitePiecewiseAffineOn_displacement ht r
  exact (hd.postcomp (ε • ContinuousAffineMap.id ℝ ℝ)).congr
    (fun _ _ => rfl)

theorem finitePiecewiseAffineOn_phase_pair {u : E → F} {t : E → ℝ}
    {S : Set E} (hu : FinitePiecewiseAffineOn u S)
    (ht : FinitePiecewiseAffineOn t S) (r ε : ℝ) :
    FinitePiecewiseAffineOn
      (fun x => (u x, ε * displacement r (t x))) S :=
  hu.prod_mk (finitePiecewiseAffineOn_scaled_displacement ht r ε)

end CollarCollapse
