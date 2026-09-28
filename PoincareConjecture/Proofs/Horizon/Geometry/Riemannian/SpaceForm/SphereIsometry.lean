import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.SphereDistance
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Diffeomorph

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace Poincare.Geometry.Riemannian.SpaceForm

private theorem sphere_chord_le_two {n : ℕ} (x y : UnitSphere n) : dist x y ≤ 2 := by
  have hx : ‖(x : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using x.property
  have hy : ‖(y : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using y.property
  simpa only [Subtype.dist_eq, dist_eq_norm, hx, hy, one_add_one_eq_two] using
    norm_sub_le (x : EuclideanSpace ℝ (Fin (n + 1))) y

theorem roundSphere_diffeomorph_isometry {n : ℕ} (hn : 1 ≤ n)
    (e : Diffeomorph (𝓡 n) (𝓡 n) (UnitSphere n) (UnitSphere n) ∞)
    (hinner : ∀ x : UnitSphere n, ∀ v w : TangentSpace (𝓡 n) x,
      (roundSphereMetric n).inner x v w = (roundSphereMetric n).inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w)) :
    Isometry e := by
  apply Isometry.of_dist_eq
  intro x y
  have h := (roundSphereMetric n).edist_diffeomorph (roundSphereMetric n) e hinner x y
  rw [roundSphereMetric_edist_eq_angle hn, roundSphereMetric_edist_eq_angle hn] at h
  have ha : Real.arccos (1 - dist x y ^ 2 / 2) =
      Real.arccos (1 - dist (e x) (e y) ^ 2 / 2) := by
    simpa only [ENNReal.toReal_ofReal (Real.arccos_nonneg _)] using
      congrArg ENNReal.toReal h
  have hb (p q : UnitSphere n) : -1 ≤ 1 - dist p q ^ 2 / 2 ∧
      1 - dist p q ^ 2 / 2 ≤ 1 := by
    have hd := sphere_chord_le_two p q
    have hd0 := dist_nonneg (x := p) (y := q)
    constructor <;> nlinarith [sq_nonneg (dist p q)]
  have hc := congrArg Real.cos ha
  rw [Real.cos_arccos (hb x y).1 (hb x y).2,
    Real.cos_arccos (hb (e x) (e y)).1 (hb (e x) (e y)).2] at hc
  nlinarith [dist_nonneg (x := x) (y := y), dist_nonneg (x := e x) (y := e y)]

end Poincare.Geometry.Riemannian.SpaceForm
