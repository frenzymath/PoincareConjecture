import PoincareConjecture.Proofs.M35.RadialGauge.EuclideanGauge
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.Instances.Real










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped ContDiff Manifold NNReal

namespace PoincareConjecture.M35.RadialGauge

variable {n : ℕ}

local notation "V" => EuclideanSpace ℝ (Fin (n + 1))



theorem exists_euclideanGauge_diffeomorph {u : V → ℝ} (hu : ContDiff ℝ ∞ u)
    (hv : ∀ x, (1 + ‖x‖) * |u x| ≤ 1 / 8)
    (hd : ∀ x, (1 + ‖x‖) * ‖fderiv ℝ u x‖ ≤ 1 / 8) :
    ∃ Φ : Diffeomorph (𝓡 (n + 1)) (𝓡 (n + 1)) V V ∞,
      (Φ : V → V) = euclideanGauge u := by
  have hs : ContDiff ℝ ∞ (euclideanGauge u) := (hu.exp).smul contDiff_id
  have hclose (x : V) : ‖fderiv ℝ (euclideanGauge u) x -
      ContinuousLinearMap.id ℝ V‖ ≤ 1 / 2 := by
    have h := euclideanGauge_sub_id_fderiv_bound
      (hu.differentiable (by simp) x) (hv x) (hd x)
    change ‖fderiv ℝ (fun y => euclideanGauge u y - id y) x‖ ≤ 1 / 2 at h
    rw [fderiv_fun_sub (hs.differentiable (by simp) x) differentiableAt_id,
      fderiv_id] at h
    exact h
  obtain ⟨e, he, hes, hei⟩ :=
    Poincare.Analysis.Calculus.exists_smooth_homeomorph_of_fderiv_close_id
      hs (by norm_num : (1 / 2 : ℝ≥0) < 1) hclose
  exact ⟨{ toEquiv := e.toEquiv
           contMDiff_toFun := hes.contMDiff
           contMDiff_invFun := hei.contMDiff }, he⟩


theorem euclideanGauge_zero (u : V → ℝ) : euclideanGauge u 0 = 0 := by
  simp only [euclideanGauge, smul_zero]



theorem euclideanGauge_equivariant (L : V ≃ₗᵢ[ℝ] V) {u : V → ℝ}
    (hu : ∀ x, u (L x) = u x) (x : V) :
    euclideanGauge u (L x) = L (euclideanGauge u x) := by
  simp only [euclideanGauge, hu, map_smul]

end PoincareConjecture.M35.RadialGauge
