import PoincareConjecture.Proofs.M01.NormalizationCharts
import PoincareConjecture.Proofs.M01.NormalizationLocalDistance









set_option autoImplicit false

open Bundle Manifold Metric Set Filter
open scoped Manifold ContDiff Topology ENNReal NNReal

universe u

namespace PoincareConjecture

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type u} [EMetricSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) 1 M]
  [RiemannianBundle (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [IsContinuousRiemannianBundle E (TangentSpace 𝓘(ℝ, E) : M → Type _)]
  [∀ z : E, NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) z)]
  [∀ z : E, NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) z)]
  [IsRiemannianManifold 𝓘(ℝ, E) M]


theorem m01_exists_bilipschitz_chart (x : M) (C : ℝ≥0) (hC : 1 < C) :
    ∃ e : OpenPartialHomeomorph M (TangentSpace 𝓘(ℝ, E) x),
      ∃ R : ℝ, 0 < R ∧ x ∈ e.source ∧
        Metric.ball (e x) R ⊆ e.target ∧
        LipschitzOnWith C e.symm (Metric.ball (e x) R) ∧
        LipschitzOnWith C e (e.symm '' Metric.ball (e x) R) := by
  obtain ⟨e, hxe, hf, hh, hdf, hdh⟩ :=
    m01_exists_normalizedChart (E := E) x (C := (C : ℝ)) (by exact_mod_cast hC)
  obtain ⟨U, hUsub, hUopen, hxU⟩ := mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds hxe) hdf)
  obtain ⟨ε, hε, hεU⟩ := EMetric.mem_nhds_iff.mp (hUopen.mem_nhds hxU)
  obtain ⟨δ, hδ, hδε⟩ :=
    ENNReal.exists_nnreal_pos_mul_lt (a := (3 : ℝ≥0∞)) (by norm_num) hε.ne'
  have hball : Metric.eball x (3 * (δ : ℝ≥0∞)) ⊆ U := by
    apply (Metric.eball_subset_eball ?_).trans hεU
    simpa only [mul_comm] using hδε.le
  have hδe : 0 < (δ : ℝ≥0∞) := by exact_mod_cast hδ
  have hLip : LipschitzOnWith C e (Metric.eball x δ) := by
    apply m01_lipschitzOnWith_of_mfderiv_bound_ball hUopen
      (hf.mono (fun y hy => (hUsub hy).1)) C (zero_lt_one.trans hC) _ x δ hδ hball
    intro y hy
    have h : ‖mfderiv 𝓘(ℝ, E) 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) e y‖ < (C : ℝ) :=
      (hUsub hy).2
    simp only [enorm, nnnorm]
    exact_mod_cast h.le
  have hnear : e.symm ⁻¹' Metric.eball x δ ∈ 𝓝 (e x) := by
    have hcont : ContinuousAt e.symm (e x) := e.continuousAt_symm (e.map_source hxe)
    apply hcont.preimage_mem_nhds
    rw [e.left_inv hxe]
    exact Metric.eball_mem_nhds x hδe
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (inter_mem (e.open_target.mem_nhds (e.map_source hxe)) hdh) hnear)
  have htarget : Metric.ball (e x) R ⊆ e.target := fun a ha => (hRsub ha).1.1
  have himage : e.symm '' Metric.ball (e x) R ⊆ Metric.eball x δ := by
    rintro _ ⟨a, ha, rfl⟩
    exact (hRsub ha).2
  refine ⟨e, R, hR, hxe, htarget, ?_, hLip.mono himage⟩
  intro a ha b hb
  rw [IsRiemannianManifold.out (I := 𝓘(ℝ, E))]
  apply m01_riemannianEDist_le_of_mfderiv_bound_convex e.open_target hh
    (convex_ball _ _) htarget C _ ha hb
  intro z hz
  have h : ‖mfderiv 𝓘(ℝ, TangentSpace 𝓘(ℝ, E) x) 𝓘(ℝ, E) e.symm z‖ < (C : ℝ) :=
    (hRsub hz).1.2
  simp only [enorm, nnnorm]
  exact_mod_cast h.le

end PoincareConjecture
