import PoincareConjecture.Proofs.M28.Mathlib.RelativeBilinearComparison
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.Order.Basic











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology





theorem ContinuousLinearMap.eventually_mutual_quadratic_bounds_of_uniform_squeeze
    {E X I : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter I} {S : Set X}
    (A : X → E →L[ℝ] E →L[ℝ] ℝ)
    (B C : I → X → E →L[ℝ] E →L[ℝ] ℝ)
    {alpha : ℝ} (halpha : 0 < alpha)
    (hlower : ∀ x ∈ S, ∀ v, alpha * ‖v‖ ^ 2 ≤ A x v v)
    (hlimit : TendstoUniformlyOn B A l S)
    (lower upper : I → ℝ)
    (hlowerLimit : Tendsto lower l (𝓝 1))
    (hupperLimit : Tendsto upper l (𝓝 1))
    (hsqueeze : ∀ᶠ i in l, ∀ x ∈ S, ∀ v,
      lower i * B i x v v ≤ C i x v v ∧ C i x v v ≤ upper i * B i x v v) :
    ∀ c : ℝ, 1 < c → ∀ᶠ i in l, ∀ x ∈ S, ∀ v,
      C i x v v ≤ c ^ 2 * A x v v ∧ A x v v ≤ c ^ 2 * C i x v v := by
  intro c hc
  have hcpos : 0 < c := zero_lt_one.trans hc
  have htau : 0 < c - 1 := sub_pos.mpr hc
  have hconstant : 1 + (c - 1) = c := by ring
  have htol : 0 < ((c - 1) / (1 + (c - 1))) * alpha := by
    rw [hconstant]
    exact mul_pos (div_pos htau hcpos) halpha
  have hinv : c⁻¹ < 1 := (inv_lt_one₀ hcpos).mpr hc
  filter_upwards [(Metric.tendstoUniformlyOn_iff
    (α := E →L[ℝ] E →L[ℝ] ℝ) (β := X) (ι := I)).mp hlimit _ htol,
    (tendsto_order.mp hlowerLimit).1 (c⁻¹) hinv,
    (tendsto_order.mp hupperLimit).2 c hc, hsqueeze] with i hclose hlo hup hsq
  intro x hx v
  have hrelative := ContinuousLinearMap.relative_quadratic_bounds_of_norm_sub_le
    (A x) (B i x) halpha htau (hlower x hx)
    (by
      have hnorm := dist_eq_norm' (A x) (B i x)
      simpa only [hnorm] using (hclose x hx).le) v
  rw [hconstant] at hrelative
  have hAnonneg : 0 ≤ A x v v :=
    (mul_nonneg halpha.le (sq_nonneg ‖v‖)).trans (hlower x hx v)
  have hBnonneg : 0 ≤ B i x v v :=
    (mul_nonneg (inv_nonneg.mpr hcpos.le) hAnonneg).trans hrelative.1
  constructor
  · calc
      C i x v v ≤ upper i * B i x v v := (hsq x hx v).2
      _ ≤ c * B i x v v := mul_le_mul_of_nonneg_right hup.le hBnonneg
      _ ≤ c * (c * A x v v) := mul_le_mul_of_nonneg_left hrelative.2 hcpos.le
      _ = c ^ 2 * A x v v := by ring
  · have hlow : c⁻¹ * (c⁻¹ * A x v v) ≤ C i x v v :=
      (mul_le_mul_of_nonneg_left hrelative.1 (inv_nonneg.mpr hcpos.le)).trans
        ((mul_le_mul_of_nonneg_right hlo.le hBnonneg).trans (hsq x hx v).1)
    have hmul := mul_le_mul_of_nonneg_left hlow (sq_nonneg c)
    have hcancel : c ^ 2 * (c⁻¹ * (c⁻¹ * A x v v)) = A x v v := by
      field_simp [hcpos.ne']
    rwa [hcancel] at hmul
