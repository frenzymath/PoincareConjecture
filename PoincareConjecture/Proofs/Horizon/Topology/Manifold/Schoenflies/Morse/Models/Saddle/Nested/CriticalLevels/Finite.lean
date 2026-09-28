import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Nested.CriticalPoint
import Mathlib.Algebra.Polynomial.Roots



noncomputable section
set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Nested

private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S2 := sphere (0 : E3) 1

theorem critical_latitude_ne_half {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) : (p : E3) 2 ≠ 1 / 2 := by
  intro hz
  have h := (critical_point_coordinates hp).2
  rw [hz] at h
  norm_num at h

theorem critical_polynomial_eq_zero {p : S2}
    (hp : mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0) :
    criticalPolynomial ((p : E3) 2) = 0 := by
  obtain ⟨hy, hc⟩ := critical_point_coordinates hp
  have hn : ((p : E3) 0)^2 = 1 - ((p : E3) 2)^2 := by
    have hn := EuclideanSpace.norm_sq_eq (p : E3)
    simp [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hy] at hn
    nlinarith
  have hm : (p : E3) 0 * (2 * (p : E3) 2 - 1) = -((3 / 10) * (p : E3) 2) := by
    linarith
  have hs := congrArg (fun t : Real => t^2) hm
  rw [mul_pow, neg_sq, mul_pow, hn] at hs
  dsimp [criticalPolynomial]
  nlinarith


theorem critical_latitude_injOn :
    InjOn (fun p : S2 => (p : E3) 2)
      {p | mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0} := by
  intro p hp q hq hz
  change (p : E3) 2 = (q : E3) 2 at hz
  obtain ⟨hpy, hpc⟩ := critical_point_coordinates hp
  obtain ⟨hqy, hqc⟩ := critical_point_coordinates hq
  have hn : 2 * (p : E3) 2 - 1 ≠ 0 := by
    intro he
    exact critical_latitude_ne_half hp (by linarith)
  have hx : (p : E3) 0 = (q : E3) 0 := by
    rw [← hz] at hqc
    have he : ((p : E3) 0 - (q : E3) 0) * (2 * (p : E3) 2 - 1) = 0 := by
      nlinarith
    exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_right hn)
  apply Subtype.ext
  ext i
  fin_cases i
  · exact hx
  · exact hpy.trans hqy.symm
  · exact hz

theorem finite_critical_polynomial_roots : {z : Real | criticalPolynomial z = 0}.Finite := by
  let P : Polynomial Real :=
    (1 - Polynomial.X^2) * (2 * Polynomial.X - 1)^2 - Polynomial.C (9 / 100) * Polynomial.X^2
  have hP : P ≠ 0 := by
    intro hp
    have h := congrArg (Polynomial.eval (0 : Real)) hp
    norm_num [P] at h
  convert Polynomial.finite_setOfPred_isRoot hP using 1
  ext z
  simp [Polynomial.IsRoot, P, criticalPolynomial]

theorem finite_critical_points :
    {p : S2 | mfderiv (𝓡 2) 𝓘(Real, Real) height p = 0}.Finite := by
  apply Set.Finite.of_finite_image (f := fun p : S2 => (p : E3) 2) ?_ critical_latitude_injOn
  apply finite_critical_polynomial_roots.subset
  rintro z ⟨p, hp, rfl⟩
  exact critical_polynomial_eq_zero hp

end Poincare.Manifold.Schoenflies.Saddle.Nested
