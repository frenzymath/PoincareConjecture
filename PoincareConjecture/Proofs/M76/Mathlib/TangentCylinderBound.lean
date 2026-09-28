import PoincareConjecture.Proofs.M76.Mathlib.TangentCylinderProjection

set_option autoImplicit false

open Set

namespace ContinuousLinearMap

variable {E F T : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup T] [NormedSpace ℝ T]

theorem exists_pos_secant_bound_tangentCylinderProjection
    (B : E →L[ℝ] F) (A : E →L[ℝ] T) {S : Set E} {c : ℝ} (hc : 0 < c)
    (hb : ∀ x ∈ S, ∀ y ∈ S, c * ‖x - y‖ ≤ ‖B x - B y‖) :
    ∃ d : ℝ, 0 < d ∧ ∀ x ∈ S ×ˢ (univ : Set T), ∀ y ∈ S ×ˢ (univ : Set T),
      d * ‖x - y‖ ≤ ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
  let e := (ContinuousLinearEquiv.refl ℝ E).skewProd (ContinuousLinearEquiv.refl ℝ T) A
  let c0 : ℝ := min c 1
  have hc0 : 0 < c0 := lt_min hc one_pos
  let k : ℝ := ‖e.symm.toContinuousLinearMap‖
  have hk : 0 ≤ k := norm_nonneg _
  have hden : 0 < k + 1 := by linarith
  refine ⟨c0 / (k + 1), div_pos hc0 hden, fun x hx y hy => ?_⟩
  have hnormal : c0 * ‖x.1 - y.1‖ ≤ ‖B x.1 - B y.1‖ :=
    (mul_le_mul_of_nonneg_right (min_le_left c 1) (norm_nonneg _)).trans
      (hb x.1 hx.1 y.1 hy.1)
  have htangent : c0 * ‖(e (x - y)).2‖ ≤ ‖(e (x - y)).2‖ := by
    exact (mul_le_mul_of_nonneg_right (min_le_right c 1) (norm_nonneg _)).trans_eq
      (one_mul _)
  have heQ : tangentCylinderProjection B A x - tangentCylinderProjection B A y =
      (B x.1 - B y.1, (e (x - y)).2) := by
    apply Prod.ext
    · rfl
    · change (x.2 + A x.1) - (y.2 + A y.1) = (x.2 - y.2) + A (x.1 - y.1)
      rw [map_sub]
      abel
  have hout : c0 * ‖e (x - y)‖ ≤
      ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
    rw [heQ, Prod.norm_def, Prod.norm_def]
    change c0 * max ‖x.1 - y.1‖ ‖(e (x - y)).2‖ ≤ _
    rw [mul_max_of_nonneg _ _ hc0.le]
    exact max_le_max hnormal htangent
  have hinv : ‖x - y‖ ≤ k * ‖e (x - y)‖ := by
    simpa only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.symm_apply_apply] using
      e.symm.toContinuousLinearMap.le_opNorm (e (x - y))
  have hi := mul_le_mul_of_nonneg_left hinv hc0.le
  have ho := mul_le_mul_of_nonneg_left hout hk
  calc
    c0 / (k + 1) * ‖x - y‖ = (c0 * ‖x - y‖) / (k + 1) := by ring
    _ ≤ ‖tangentCylinderProjection B A x - tangentCylinderProjection B A y‖ := by
      apply (div_le_iff₀ hden).mpr
      nlinarith only [hi, ho,
        norm_nonneg (tangentCylinderProjection B A x - tangentCylinderProjection B A y)]

end ContinuousLinearMap
