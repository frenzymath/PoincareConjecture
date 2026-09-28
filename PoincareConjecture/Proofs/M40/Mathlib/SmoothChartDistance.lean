import PoincareConjecture.Proofs.M40.Mathlib.SmoothChartNormalization
import PoincareConjecture.Proofs.M40.Mathlib.RiemannianVectorNorm
import PoincareConjecture.Proofs.M01.NormalizationLocalDistance














set_option autoImplicit false

noncomputable section

open Bundle Filter Set
open scoped Topology Manifold ContDiff ENNReal NNReal

namespace PoincareConjecture.M40

variable {E H M F : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H}
  [EMetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
  [IsRiemannianManifold I M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]




theorem normalizedSmoothChart_exists_lipschitz_ball
    (e : OpenPartialHomeomorph M F) (he : e.MDifferentiable I 𝓘(ℝ, F))
    {x : M} (hx : x ∈ e.source)
    (hs : ContMDiffOn I 𝓘(ℝ, F) ∞ e e.source)
    (hi : ContMDiffOn 𝓘(ℝ, F) I ∞ e.symm e.target)
    (C : ℝ≥0) (hC : 1 < C) :
    let n := normalizedSmoothChart e he hx
    ∃ R : ℝ, 0 < R ∧ Metric.ball (n x) R ⊆ n.target ∧
      LipschitzOnWith C n.symm (Metric.ball (n x) R) ∧
      LipschitzOnWith C n (n.symm '' Metric.ball (n x) R) := by
  let n := normalizedSmoothChart e he hx
  have hsource : x ∈ n.source := by
    simpa only [n, normalizedSmoothChart_source] using hx
  have hf : ContMDiffOn I 𝓘(ℝ, TangentSpace I x) 1 n n.source :=
    (normalizedSmoothChart_contMDiffOn e he hx hs).of_le (by norm_num)
  have hg : ContMDiffOn 𝓘(ℝ, TangentSpace I x) I 1 n.symm n.target :=
    (normalizedSmoothChart_symm_contMDiffOn e he hx hi).of_le (by norm_num)
  obtain ⟨hforward, hinverse⟩ :=
    normalizedSmoothChart_eventually_norm_mfderiv_lt e he hx hs hi
      (C := (C : ℝ)) (by exact_mod_cast hC)
  have hwindow : {y | y ∈ n.source ∧
      ‖mfderiv I 𝓘(ℝ, TangentSpace I x) n y‖ < (C : ℝ)} ∈ 𝓝 x :=
    inter_mem (n.open_source.mem_nhds hsource) hforward
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp hwindow
  obtain ⟨r, hrpos, hrU⟩ := EMetric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  obtain ⟨d, hdpos, hdsmall⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (a := (3 : ℝ≥0∞)) (by norm_num) hrpos.ne'
  have hdU : Metric.eball x (3 * (d : ℝ≥0∞)) ⊆ U :=
    (Metric.eball_subset_eball (by simpa only [mul_comm] using hdsmall.le)).trans hrU
  have hforwardLip : LipschitzOnWith C n (Metric.eball x d) := by
    apply m01_lipschitzOnWith_of_mfderiv_bound_ball hUopen
      (hf.mono (fun y hy => (hUsub hy).1)) C (zero_lt_one.trans hC) _ x d hdpos hdU
    intro y hy
    exact mfderiv_enorm_le_vector_target (hUsub hy).2.le
  have hreturn : n.symm ⁻¹' Metric.eball x d ∈ 𝓝 (n x) := by
    apply (n.continuousAt_symm (n.map_source hsource)).preimage_mem_nhds
    rw [n.left_inv hsource]
    exact Metric.eball_mem_nhds x (by exact_mod_cast hdpos)
  have hcoordinateWindow : {z | z ∈ n.target ∧
      ‖mfderiv 𝓘(ℝ, TangentSpace I x) I n.symm z‖ < (C : ℝ) ∧
      n.symm z ∈ Metric.eball x d} ∈ 𝓝 (n x) := by
    filter_upwards [n.open_target.mem_nhds (n.map_source hsource),
      hinverse, hreturn] with z hz hzderiv hzreturn
    exact ⟨hz, hzderiv, hzreturn⟩
  obtain ⟨R, hRpos, hRwindow⟩ := Metric.mem_nhds_iff.mp hcoordinateWindow
  have htarget : Metric.ball (n x) R ⊆ n.target := fun z hz => (hRwindow hz).1
  refine ⟨R, hRpos, htarget, ?_, ?_⟩
  · intro a ha b hb
    rw [IsRiemannianManifold.out (I := I)]
    apply m01_riemannianEDist_le_of_mfderiv_bound_convex n.open_target hg
      (convex_ball _ _) htarget C _ ha hb
    intro z hz
    exact mfderiv_enorm_le_vector_source (hRwindow hz).2.1.le
  · apply hforwardLip.mono
    rintro y ⟨z, hz, rfl⟩
    exact (hRwindow hz).2.2

end PoincareConjecture.M40
