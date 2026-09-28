import PoincareConjecture.Proofs.M40.Mathlib.LipschitzSmoothingRiemannian
import PoincareConjecture.Proofs.M40.Mathlib.RiemannianVectorNorm
import PoincareConjecture.Proofs.M01.NormalizationLocalDistance












set_option autoImplicit false

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal NNReal

universe uE uH uM uF

namespace PoincareConjecture.M40

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type uE)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type uE)]
  [IsRiemannianManifold I M]
  {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]





theorem exists_lipschitzOn_nhds_of_contMDiffAt
    {f : M → F} {x : M} (hf : ContMDiffAt I 𝓘(ℝ, F) 1 f x) :
    ∃ A : ℝ≥0, 0 < A ∧ ∃ U ∈ 𝓝 x, LipschitzOnWith A f U := by
  letI : IsContinuousRiemannianBundle F (TangentSpace 𝓘(ℝ, F) : F → Type uF) :=
    ⟨⟨(riemannianMetricVectorSpace F).inner,
      (riemannianMetricVectorSpace F).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let A : ℝ≥0 := ⟨‖mfderiv I 𝓘(ℝ, F) f x‖ + 1, by positivity⟩
  have hA : 0 < A := by
    change 0 < ‖mfderiv I 𝓘(ℝ, F) f x‖ + 1
    positivity
  have hbound : ∀ᶠ y in 𝓝 x, ‖mfderiv I 𝓘(ℝ, F) f y‖ < (A : ℝ) :=
    eventually_norm_mfderiv_lt hf (by change _ < _ + 1; linarith)
  obtain ⟨V, hV, hfV⟩ :=
    (contMDiffAt_iff_contMDiffOn_nhds (n := 1) (by norm_num)).mp hf
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp (inter_mem hV hbound)
  obtain ⟨r, hr, hrU⟩ := EMetric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  obtain ⟨δ, hδ, hδr⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (a := (3 : ℝ≥0∞)) (by norm_num) hr.ne'
  have htriple : eball x (3 * (δ : ℝ≥0∞)) ⊆ U := by
    apply (eball_subset_eball ?_).trans hrU
    simpa only [mul_comm] using hδr.le
  have hLip : LipschitzOnWith A f (eball x δ) := by
    apply m01_lipschitzOnWith_of_mfderiv_bound_ball hUopen
      (hfV.mono (fun y hy => (hUsub hy).1)) A hA ?_ x δ hδ htriple
    intro y hy
    exact mfderiv_enorm_le_vector_target (hUsub hy).2.le
  refine ⟨A, hA, eball x δ, eball_mem_nhds x ?_, hLip⟩
  exact_mod_cast hδ

end PoincareConjecture.M40
