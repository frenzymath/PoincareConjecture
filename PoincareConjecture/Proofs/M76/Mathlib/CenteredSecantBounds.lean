import PoincareConjecture.Proofs.M76.Mathlib.TangentCylinderBound
import PoincareConjecture.Proofs.M76.Mathlib.OrthogonalCylinderCoordinates










set_option autoImplicit false

open Set

namespace ContinuousLinearEquiv

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]





theorem exists_pos_secant_bound_of_centered_image (e : E ≃L[ℝ] G)
    (Q : E →L[ℝ] F) (p : E) {S : Set E} {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ (fun z => e (z - p)) '' S,
      ∀ y ∈ (fun z => e (z - p)) '' S,
        c * ‖x - y‖ ≤ ‖Q (e.symm x) - Q (e.symm y)‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S, ∀ y ∈ S, d * ‖x - y‖ ≤ ‖Q x - Q y‖ := by
  let k : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hk : 0 ≤ k := norm_nonneg _
  have hden : 0 < k + 1 := by linarith
  refine ⟨c / (k + 1), div_pos hc hden, fun x hx y hy => ?_⟩
  have h := hb _ (mem_image_of_mem _ hx) _ (mem_image_of_mem _ hy)
  have hcoord : e (x - p) - e (y - p) = e (x - y) := by
    rw [← map_sub, sub_sub_sub_cancel_right]
  have hout : Q (x - p) - Q (y - p) = Q x - Q y := by
    rw [Q.map_sub, Q.map_sub]
    abel
  rw [hcoord, e.symm_apply_apply, e.symm_apply_apply, hout] at h
  have hinv : ‖x - y‖ ≤ k * ‖e (x - y)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_opNorm (e (x - y))
  have hi := mul_le_mul_of_nonneg_left hinv hc.le
  have ho := mul_le_mul_of_nonneg_left h hk
  calc
    c / (k + 1) * ‖x - y‖ = (c * ‖x - y‖) / (k + 1) := by ring
    _ ≤ ‖Q x - Q y‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hi, ho, norm_nonneg (Q x - Q y)]

end ContinuousLinearEquiv
