import PoincareConjecture.Proofs.M47.NoncollapseHorizonScales

set_option autoImplicit false

open Set
open scoped ENNReal

namespace PoincareConjecture.M47

theorem limitNoncollapse_theta_ninth_squeeze {kappa r : ℝ} {V : ℝ≥0∞}
    (hvolume : ∀ theta ∈ Ioo (0 : ℝ) 1,
      ENNReal.ofReal (kappa * theta ^ 9 * r ^ 3) ≤ V) :
    ENNReal.ofReal (kappa * r ^ 3) ≤ V := by
  exact PoincareConjecture.Proofs.M47.horizon_volume_of_contracted_densities hvolume

theorem limitNoncollapse_theta_radius {theta r : ℝ}
    (htheta : 0 < theta) (_hupper : theta < 1) :
    0 < theta ^ 2 * r ↔ 0 < r := by
  constructor
  · intro h
    nlinarith [sq_pos_of_pos (show 0 < theta from htheta)]
  · intro hr
    positivity

end PoincareConjecture.M47
