import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Smoothing.Local.Riemannian
import PoincareLib.Geometry.RicciFlow.Surgery.Comparison.Distance.VectorNorm
import PoincareLib.Geometry.Riemannian.Normalization.Volume.LocalDistance
/-!
# Local Lipschitz bounds for smooth cutoff functions

A map which is C1 at a point has a finite local Lipschitz bound for the
actual Riemannian source distance. The derivative bound is transported
to the canonical vector-space target tangent norm and then integrated
along near-minimizing paths using the published M01 local ball theorem.
This supplies the cutoff constant in the quantitative smoothing argument
of the SurgeryComparison.Transport full contract, Morgan--Tian Claim 18.22, printed p. 433.
-/

set_option autoImplicit false

open Bundle Set Filter Metric
open scoped Topology Manifold ContDiff ENNReal NNReal

universe uE uH uM uF

namespace PoincareMT.SurgeryComparison.Transport

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type uM} [EMetricSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [RiemannianBundle (TangentSpace I : M → Type uE)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type uE)]
  [IsRiemannianManifold I M]
  {F : Type uF} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A C1 map into a real inner product space is Lipschitz on a neighborhood
of each point, measured in the actual Riemannian source distance. The
positive finite bound supplies the cutoff-error constant in the SurgeryComparison.Transport full
contract, Morgan--Tian Claim 18.22, p. 433. -/
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
    apply normalization_lipschitzOnWith_of_mfderiv_bound_ball hUopen
      (hfV.mono (fun y hy => (hUsub hy).1)) A hA ?_ x δ hδ htriple
    intro y hy
    exact mfderiv_enorm_le_vector_target (hUsub hy).2.le
  refine ⟨A, hA, eball x δ, eball_mem_nhds x ?_, hLip⟩
  exact_mod_cast hδ

end PoincareMT.SurgeryComparison.Transport
