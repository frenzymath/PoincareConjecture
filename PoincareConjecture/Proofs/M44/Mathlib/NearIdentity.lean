import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.UniformSpace.UniformConvergence










set_option autoImplicit false

open Set Filter
open scoped Topology



theorem Convex.norm_image_sub_ge_of_norm_fderiv_sub_id_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (hU : Convex ℝ U) {c : ℝ}
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ U, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c)
    {x y : E} (hx : x ∈ U) (hy : y ∈ U) :
    (1 - c) * ‖y - x‖ ≤ ‖f y - f x‖ := by
  have h := hU.norm_image_sub_le_of_norm_fderiv_le' hf hbound hx hy
  simp only [ContinuousLinearMap.id_apply] at h
  have hn := norm_le_norm_sub_add (y - x) (f y - f x)
  rw [norm_sub_rev (y - x) (f y - f x)] at hn
  nlinarith



theorem Convex.injOn_of_norm_fderiv_sub_id_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → E} {U : Set E} (hU : Convex ℝ U) {c : ℝ} (hc : c < 1)
    (hf : ∀ x ∈ U, DifferentiableAt ℝ f x)
    (hbound : ∀ x ∈ U, ‖fderiv ℝ f x - ContinuousLinearMap.id ℝ E‖ ≤ c) :
    InjOn f U := by
  intro x hx y hy hxy
  have h := hU.norm_image_sub_ge_of_norm_fderiv_sub_id_le hf hbound hx hy
  rw [hxy, sub_self, norm_zero] at h
  have hn : ‖y - x‖ = 0 := by nlinarith [norm_nonneg (y - x)]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hn)).symm



theorem TendstoUniformlyOn.eventually_injOn_of_fderiv_tendsto_id
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l : Filter ι} {f : ι → E → E} {U : Set E} (hU : Convex ℝ U)
    (hf : ∀ i x, x ∈ U → DifferentiableAt ℝ (f i) x)
    (hlim : TendstoUniformlyOn (fun i x => fderiv ℝ (f i) x)
      (fun _ => ContinuousLinearMap.id ℝ E) l U) :
    ∀ᶠ i in l, InjOn (f i) U := by
  have h := Metric.tendstoUniformlyOn_iff.mp hlim (1 / 2) (by norm_num)
  filter_upwards [h] with i hi
  apply hU.injOn_of_norm_fderiv_sub_id_le (c := 1 / 2) (by norm_num) (hf i)
  intro x hx
  simpa only [dist_eq_norm, norm_sub_rev] using (hi x hx).le



theorem TendstoUniformlyOn.eventually_bijective_of_tendsto_id
    {E P ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {l : Filter ι} {L : ι → P → E →L[ℝ] E} {U : Set P}
    (hlim : TendstoUniformlyOn L (fun _ => ContinuousLinearMap.id ℝ E) l U) :
    ∀ᶠ i in l, ∀ x ∈ U, Function.Bijective (L i x) := by
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim 1 zero_lt_one] with i hi
  intro x hx
  have hid : (1 : E →L[ℝ] E) = ContinuousLinearMap.id ℝ E := rfl
  have hnorm : ‖(1 : E →L[ℝ] E) - L i x‖ < 1 := by
    simpa only [hid, dist_eq_norm] using hi x hx
  have hu : IsUnit (L i x) := by
    simpa only [sub_sub_cancel] using isUnit_one_sub_of_norm_lt_one hnorm
  have heq : ((ContinuousLinearEquiv.ofUnit hu.unit : E ≃L[ℝ] E) : E →L[ℝ] E) =
      L i x := hu.unit_spec
  exact heq ▸ (show Function.Bijective
    (((ContinuousLinearEquiv.ofUnit hu.unit : E ≃L[ℝ] E) : E →L[ℝ] E)) from
      (ContinuousLinearEquiv.ofUnit hu.unit).bijective)
