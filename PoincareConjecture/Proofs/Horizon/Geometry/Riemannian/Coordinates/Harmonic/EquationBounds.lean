import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RicciBounds
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.RicciContraction

noncomputable section
set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

theorem abs_laplacian_metric_le_of_harmonic (D : LeviCivitaData g)
    {x : EuclideanSpace ℝ (Fin n)}
    (hharm : ∀ᶠ y in 𝓝 x, ∀ i : Fin n,
      D.laplacian (fun z : EuclideanSpace ℝ (Fin n) => z i) y = 0)
    {a b K : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb : 1 ≤ b)
    (hlower : ∀ v : EuclideanSpace ℝ (Fin n), a * ‖v‖ ^ 2 ≤ g.inner x v v)
    (hupper : ∀ v : EuclideanSpace ℝ (Fin n), g.inner x v v ≤ b * ‖v‖ ^ 2)
    (hcurv : D.curvatureTensorNorm x ≤ K) (u v : EuclideanSpace ℝ (Fin n)) :
    |D.laplacian (fun y => g.inner y u v) x| ≤
      (2 * (n : ℝ) * K * b + (32 * (n : ℝ) ^ 2 * b / a ^ 3) *
        ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2) * ‖u‖ * ‖v‖ := by
  rw [D.laplacian_metric_eq_ricci_of_harmonic hharm u v]
  calc
    _ ≤ |-2 * D.ricci x u v| + |2 * D.harmonicRicciQuadratic x u v| :=
      abs_add_le _ _
    _ = 2 * |D.ricci x u v| + 2 * |D.harmonicRicciQuadratic x u v| := by
      simp only [abs_mul]
      norm_num
    _ ≤ 2 * ((n : ℝ) * K * b * ‖u‖ * ‖v‖) +
        2 * ((16 * (n : ℝ) ^ 2 * b / a ^ 3) *
          ‖fderiv ℝ g.euclideanCoefficients x‖ ^ 2 * ‖u‖ * ‖v‖) :=
      add_le_add
        (mul_le_mul_of_nonneg_left (D.abs_ricci_le_of_upper_ellipticity x
          (zero_le_one.trans hb) hupper hcurv u v) (by norm_num))
        (mul_le_mul_of_nonneg_left (D.abs_harmonicRicciQuadratic_le_of_ellipticity x
          ha ha1 hb hlower hupper u v) (by norm_num))
    _ = _ := by ring

end PoincareConjecture.LeviCivitaData
