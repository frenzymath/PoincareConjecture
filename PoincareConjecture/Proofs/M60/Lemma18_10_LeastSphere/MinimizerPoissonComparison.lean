import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Harmonic.EnergyBounds
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Euclidean
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationPoissonCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

noncomputable section

namespace PoincareConjecture.M60

open LeviCivitaData.Dirichlet

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "gEucl" => RiemannianMetric.euclideanMetric 2




theorem suPlane_test_poincare (D : LeviCivitaData gEucl) {R : ℝ} (hR : 0 < R) :
    HasTestPoincare D (Metric.ball (0 : Plane) R) (4 * R ^ 2) := by
  have h := HarmonicCoordinates.metric_poincare_of_ellipticity D hR
    (show (0 : ℝ) < 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num) (by
      intro x _ v
      change 1 * ‖v‖ ^ 2 ≤ (gEucl).inner x v v ∧ (gEucl).inner x v v ≤ 1 * ‖v‖ ^ 2
      simp only [RiemannianMetric.euclideanMetric_inner, real_inner_self_eq_norm_sq,
        one_mul, le_refl, and_self])
  convert! h using 1
  norm_num
  ring




theorem suPlane_poisson_weak (D : LeviCivitaData gEucl) {R : ℝ} (hR : 0 < R)
    (F : Lp ℝ 2 (gEucl).volumeMeasure) :
    ∃ w : H1Zero D (Metric.ball (0 : Plane) R),
      (∀ v, gradientEnergy D (Metric.ball (0 : Plane) R) w v =
        inner ℝ F (toL2 D (Metric.ball (0 : Plane) R) v)) ∧
      ‖toL2 D (Metric.ball (0 : Plane) R) w‖ ≤ 4 * R ^ 2 * ‖F‖ ∧
      gradientEnergy D (Metric.ball (0 : Plane) R) w w ≤ 4 * R ^ 2 * ‖F‖ ^ 2 := by
  let O := Metric.ball (0 : Plane) R
  let ell : H1Zero D O →L[ℝ] ℝ := (innerSL ℝ F).comp (toL2 D O)
  have hP := suPlane_test_poincare D hR
  have hP0 : 0 ≤ 4 * R ^ 2 := by positivity
  let w := weakDirichlet D O hP0 hP ell
  have heq (v : H1Zero D O) : gradientEnergy D O w v = inner ℝ F (toL2 D O v) :=
    weakDirichlet_spec hP0 hP ell v
  have henergy : gradientEnergy D O w w ≤ ‖F‖ * ‖toL2 D O w‖ := by
    rw [heq]
    exact real_inner_le_norm _ _
  have hL2 : ‖toL2 D O w‖ ≤ 4 * R ^ 2 * ‖F‖ := by
    have hp := norm_toL2_sq_le_gradientEnergy hP w
    have hm := mul_le_mul_of_nonneg_left henergy hP0
    by_cases hz : ‖toL2 D O w‖ = 0
    · rw [hz]
      positivity
    · have hpos : 0 < ‖toL2 D O w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      nlinarith
  refine ⟨w, heq, hL2, ?_⟩
  calc
    _ ≤ ‖F‖ * ‖toL2 D O w‖ := henergy
    _ ≤ ‖F‖ * (4 * R ^ 2 * ‖F‖) := mul_le_mul_of_nonneg_left hL2 (norm_nonneg _)
    _ = _ := by ring

end PoincareConjecture.M60

end
