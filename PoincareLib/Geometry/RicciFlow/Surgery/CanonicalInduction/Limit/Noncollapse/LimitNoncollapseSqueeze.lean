import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Noncollapse.NoncollapseHorizonScales

/-!
# Exact ninth-power density squeeze

The contracted-radius inequalities recover the unchanged kappa without
spending a canonical margin. Source: Morgan--Tian, Proposition 17.1,
pp. 407-408; reviewed noncollapse derivation, section 7.
-/

set_option autoImplicit false

open Set
open scoped ENNReal

namespace PoincareMT.M47

/-- The existing directed density limit turns every strict contraction
bound into the exact terminal-volume bound. -/
theorem limitNoncollapse_theta_ninth_squeeze {kappa r : ℝ} {V : ℝ≥0∞}
    (hvolume : ∀ theta ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) ≤ V) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ V := by
  exact PoincareMT.Proofs.M47.horizon_volume_of_contracted_densities hvolume

/-- The algebra behind the normalized physical curvature threshold retains
the same kappa after a theta-contraction. -/
theorem limitNoncollapse_theta_radius {theta r : ℝ}
    (htheta : 0 < theta) (_hupper : theta < 1) :
    0 < theta ^ 2 * r ↔ 0 < r := by
  constructor
  · intro h
    nlinarith [sq_pos_of_pos (show 0 < theta from htheta)]
  · intro hr
    positivity

end PoincareMT.M47
