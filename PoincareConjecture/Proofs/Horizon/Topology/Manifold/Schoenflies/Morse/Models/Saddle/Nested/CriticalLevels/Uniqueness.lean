import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalLevels.Finite
import Mathlib.Analysis.Calculus.Deriv.MeanValue

noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem hasDerivAt_criticalPolynomial (z : Real) :
    HasDerivAt criticalPolynomial (4 * z^2 * (3 - 4 * z) + (291 / 50) * z - 4) z := by
  convert! (((hasDerivAt_const z (1 : Real)).sub ((hasDerivAt_id z).pow 2)).mul
    ((((hasDerivAt_id z).const_mul 2).sub_const 1).pow 2)).sub
    (((hasDerivAt_id z).pow 2).const_mul (9 / 100 : Real)) using 1
  dsimp [criticalPolynomial]
  ring

theorem strictMonoOn_criticalPolynomial_saddle_interval :
    StrictMonoOn criticalPolynomial (Icc (3 / 5 : Real) (5 / 8)) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc _ _)
    (by unfold criticalPolynomial; fun_prop)
  intro z hz
  have hz' : z ∈ Icc (3 / 5 : Real) (5 / 8) := interior_subset hz
  rw [(hasDerivAt_criticalPolynomial z).deriv]
  have hs : (9 / 25 : Real) ≤ z^2 := by nlinarith [hz'.1]
  have hfactor : (1 / 2 : Real) ≤ 3 - 4 * z := by linarith [hz'.2]
  have hmul := mul_le_mul_of_nonneg_left hfactor (show 0 ≤ 4 * z^2 by positivity)
  nlinarith [hz'.1]

theorem critical_latitude_unique_in_saddle_interval {p q : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0)
    (hq : mfderiv (𝓡 2) 𝓘(Real, Real) height q = 0)
    (hpz : (p : E3) 2 ∈ Icc (3 / 5 : Real) (5 / 8))
    (hqz : (q : E3) 2 ∈ Icc (3 / 5 : Real) (5 / 8)) : p = q := by
  apply critical_latitude_injOn hp hq
  apply strictMonoOn_criticalPolynomial_saddle_interval.injOn hpz hqz
  rw [critical_polynomial_eq_zero hp, critical_polynomial_eq_zero hq]

end Poincare.Manifold.Schoenflies.Saddle.Nested
