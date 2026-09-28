import PoincareConjecture.Proofs.M76.Mathlib.RadialSimplex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact











set_option autoImplicit false

open Set NormedSpace

namespace ContinuousLinearMap

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem exists_pos_norm_lower_bound_on_cone [FiniteDimensional ℝ E]
    (Q : E →L[ℝ] F) {C : Set E} (hclosed : IsClosed C)
    (hsmul : ∀ x ∈ C, ∀ r : ℝ, 0 < r → r • x ∈ C)
    (hker : ∀ x ∈ C, Q x = 0 → x = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖ := by
  have hcompact : IsCompact (Metric.sphere (0 : E) 1 ∩ C) :=
    (isCompact_sphere (0 : E) 1).inter_right hclosed
  obtain ⟨c, hc, hb⟩ := hcompact.exists_forall_le' Q.continuous.norm.continuousOn
    (a := (0 : ℝ)) (fun x hx => by
      apply norm_pos_iff.mpr
      intro he
      have hx0 := hker x hx.2 he
      simpa [hx0] using hx.1)
  refine ⟨c, hc, fun x hx => ?_⟩
  by_cases hx0 : x = 0
  · simp [hx0]
  have hnx : normalize x ∈ Metric.sphere (0 : E) 1 ∩ C :=
    ⟨by simpa [Metric.mem_sphere] using norm_normalize hx0,
      hsmul x hx ‖x‖⁻¹ (inv_pos.mpr (norm_pos_iff.mpr hx0))⟩
  calc
    c * ‖x‖ = ‖x‖ * c := mul_comm _ _
    _ ≤ ‖x‖ * ‖Q (normalize x)‖ := mul_le_mul_of_nonneg_left (hb _ hnx) (norm_nonneg x)
    _ = ‖Q (‖x‖ • normalize x)‖ := by
      rw [map_smul, norm_smul, Real.norm_of_nonneg (norm_nonneg x)]
    _ = ‖Q x‖ := by rw [norm_smul_normalize]




theorem norm_lower_bound_of_perturbation (Q R : E →L[ℝ] F) {C : Set E} {c : ℝ}
    (hb : ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖) (hR : ‖Q - R‖ ≤ c / 2) :
    ∀ x ∈ C, (c / 2) * ‖x‖ ≤ ‖R x‖ := by
  intro x hx
  have hdiff : ‖Q x‖ - ‖R x‖ ≤ (c / 2) * ‖x‖ :=
    (norm_sub_norm_le (Q x) (R x)).trans
      ((Q - R).le_opNorm x |>.trans (mul_le_mul_of_nonneg_right hR (norm_nonneg x)))
  have h := hb x hx
  linarith




theorem norm_lower_bound_le_kernel_distance (Q : E →L[ℝ] F) {C : Set E} {c : ℝ}
    (hb : ∀ x ∈ C, c * ‖x‖ ≤ ‖Q x‖) {x k : E} (hx : x ∈ C) (hk : Q k = 0) :
    c * ‖x‖ ≤ ‖Q‖ * ‖x - k‖ := by
  have he : Q (x - k) = Q x := by rw [map_sub, hk, sub_zero]
  exact (hb x hx).trans (he ▸ Q.le_opNorm (x - k))

end ContinuousLinearMap
