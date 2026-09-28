import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.InnerProductSpace.PiL2











set_option autoImplicit false

open Set Filter Metric
open scoped Topology NNReal

namespace PoincareConjecture.M28



theorem coordinate_core_subset_image_of_fderiv_close
    {n : ℕ} {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ x ∈ closedBall 0 (ρ / 4), DifferentiableAt ℝ f x)
    (hzero : ‖f 0‖ < ρ / 16)
    (hderiv : ∀ x ∈ closedBall 0 (ρ / 4),
      ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))‖ ≤ 1 / 4) :
    closedBall 0 (ρ / 8) ⊆ f '' closedBall 0 (ρ / 4) := by
  let E := EuclideanSpace ℝ (Fin n)
  let L : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  have happrox : ApproximatesLinearOn f L (closedBall 0 (ρ / 4)) (1 / 4) := by
    intro x hx y hy
    change ‖f x - f y - L (x - y)‖ ≤ (1 / 4 : ℝ) * ‖x - y‖
    exact Convex.norm_image_sub_le_of_norm_fderiv_le' hdiff hderiv
      (convex_closedBall (0 : E) (ρ / 4)) hy hx
  let Linv : L.NonlinearRightInverse :=
    { toFun := id
      nnnorm := 1
      bound' := fun x => by simp
      right_inv' := fun _ => rfl }
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse Linv
    (b := 0) (ε := ρ / 4) (by positivity) (subset_refl _)
  have hradius : (((Linv.nnnorm : ℝ)⁻¹ - ((1 / 4 : ℝ≥0) : ℝ)) * (ρ / 4)) =
      3 * ρ / 16 := by
    norm_num [Linv]
    ring
  rw [hradius] at hsurj
  intro y hy
  apply hsurj
  have hynorm : ‖y‖ ≤ ρ / 8 := by
    simpa only [mem_closedBall, dist_zero_right] using hy
  rw [mem_closedBall, dist_eq_norm]
  exact (norm_sub_le y (f 0)).trans (by linarith)



theorem eventually_coordinate_core_subset_image
    {n : ℕ} (f : ℕ → EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    {ρ : ℝ} (hρ : 0 < ρ)
    (hdiff : ∀ᶠ k in atTop, ∀ x ∈ closedBall 0 (ρ / 4), DifferentiableAt ℝ (f k) x)
    (hzero : Tendsto (fun k => f k 0) atTop (𝓝 0))
    (hderiv : TendstoUniformlyOn (fun k x => fderiv ℝ (f k) x)
      (fun _ => ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n)))
      atTop (closedBall 0 (ρ / 4))) :
    ∀ᶠ k in atTop, closedBall 0 (ρ / 8) ⊆ f k '' closedBall 0 (ρ / 4) := by
  have hnorm : Tendsto (fun k => ‖f k 0‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_zero] using hzero.norm
  have hsmall : ∀ᶠ k in atTop, ‖f k 0‖ < ρ / 16 :=
    hnorm.eventually (gt_mem_nhds (by positivity))
  filter_upwards [hdiff, hsmall,
    Metric.tendstoUniformlyOn_iff.mp hderiv (1 / 4) (by norm_num)] with k hk h0 hD
  apply coordinate_core_subset_image_of_fderiv_close hρ hk h0
  intro x hx
  rw [← dist_eq_norm, dist_comm]
  exact (hD x hx).le

end PoincareConjecture.M28
