import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity











set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.RiemannianMetric

set_option backward.isDefEq.respectTransparency false in


theorem eventually_volumeMeasure_ball_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (p : M) {K : ℝ≥0} (hK : 1 < K) :
    ∀ᶠ r : ℝ in 𝓝[>] 0,
      g.volumeMeasure (g.ball p r) ≤ (K : ℝ≥0∞) ^ (2 * n) *
        volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ∧
      volume (Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r) ≤
        (K : ℝ≥0∞) ^ (2 * n) * g.volumeMeasure (g.ball p r) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let E := EuclideanSpace ℝ (Fin n)
  let e : OpenPartialHomeomorph E M := (chartAt E p).symm
  let x : E := (chartAt E p) p
  have hx : x ∈ e.source := (chartAt E p).map_source (mem_chart_source E p)
  have hex : e x = p := (chartAt E p).left_inv (mem_chart_source E p)
  have he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source := by
    simpa [e, E, extChartAt, OpenPartialHomeomorph.extend_coe_symm,
      OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe_symm] using
      (contMDiffOn_extChartAt_symm (I := 𝓡 n) (n := ∞) p)
  have hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target := by
    simpa [e, E, extChartAt, OpenPartialHomeomorph.extend_coe,
      OpenPartialHomeomorph.extend_source] using
      (contMDiffOn_extChartAt (I := 𝓡 n) (n := ∞) (x := p))
  have heDiff : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn (by simp), hei.mdifferentiableOn (by simp)⟩
  obtain ⟨A, hA, _⟩ := g.exists_frozenPullbackEquiv (heDiff.mfderiv_injective hx)
  obtain ⟨U, hU, hxU, hUe, hcomp⟩ :=
    g.exists_open_distortion_of_tangentNorm_comparison e he hei hx A hK
      (g.eventually_pullbackNorm_comparison
        (he.contMDiffAt (e.open_source.mem_nhds hx)) A hA hK)
  have hKpos : 0 < (K : ℝ) := lt_trans zero_lt_one hK
  have hKen : (K : ℝ≥0∞) ≠ 0 := by exact_mod_cast hKpos.ne'
  have hKreal : 1 < (K : ℝ) := hK
  have hV : e '' U ∈ 𝓝 p := by
    rw [← hex]
    exact e.image_mem_nhds hx (hU.mem_nhds hxU)
  obtain ⟨ε, hε, hεV⟩ := EMetric.mem_nhds_iff.mp hV
  have hAU : A.symm ⁻¹' U ∈ 𝓝 (A x) := by
    apply A.symm.continuous.continuousAt.preimage_mem_nhds
    simpa only [A.symm_apply_apply] using hU.mem_nhds hxU
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp hAU
  have hsmallM : ∀ᶠ r : ℝ in 𝓝[>] 0, ENNReal.ofReal r < ε :=
    (ENNReal.continuous_ofReal.continuousAt.eventually
      (gt_mem_nhds (by simpa using hε))).filter_mono nhdsWithin_le_nhds
  have hsmallE : ∀ᶠ r : ℝ in 𝓝[>] 0, (K : ℝ) * r < δ :=
    ((continuous_const.mul continuous_id).continuousAt.eventually
      (gt_mem_nhds (by simpa using hδ))).filter_mono nhdsWithin_le_nhds
  filter_upwards [hsmallM, hsmallE, self_mem_nhdsWithin] with r hrM hrE hr
  have hrpos : 0 < r := hr
  have hsmallBall : g.ball p r ⊆ e '' U := by
    intro y hy
    apply hεV
    change g.edist y p < ε
    have h := (show g.edist p y < ENNReal.ofReal r from hy).trans hrM
    simpa only [edist, Manifold.riemannianEDist_comm] using h
  have hKr : 0 < (K : ℝ) * r := mul_pos hKpos hrpos
  have hlarge : ∀ y ∈ Metric.ball (A x) ((K : ℝ) * r), A.symm y ∈ U := by
    intro y hy
    exact hδU (Metric.ball_subset_ball hrE.le hy)
  let f : E → M := e ∘ A.symm
  let ψ : M → E := A ∘ e.symm
  have hfLip : LipschitzOnWith K f (Metric.ball (A x) ((K : ℝ) * r)) := by
    intro z hz w hw
    change g.edist (f z) (f w) ≤ (K : ℝ≥0∞) * EDist.edist z w
    simpa only [f, Function.comp_apply, A.apply_symm_apply, edist] using
      (hcomp (A.symm z) (hlarge z hz) (A.symm w) (hlarge w hw)).1
  have hψLip : LipschitzOnWith K ψ (g.ball p r) := by
    intro y hy z hz
    change EDist.edist (ψ y) (ψ z) ≤ (K : ℝ≥0∞) * g.edist y z
    obtain ⟨v, hv, rfl⟩ := hsmallBall hy
    obtain ⟨w, hw, rfl⟩ := hsmallBall hz
    simpa only [ψ, Function.comp_apply, e.left_inv (hUe hv), e.left_inv (hUe hw),
      edist] using
      (hcomp v hv w hw).2
  have hcover : g.ball p r ⊆ f '' Metric.ball (A x) ((K : ℝ) * r) := by
    intro y hy
    obtain ⟨v, hv, rfl⟩ := hsmallBall hy
    refine ⟨A v, ?_, by simp [f]⟩
    apply edist_lt_ofReal.mp
    calc
      EDist.edist (A v) (A x) ≤ (K : ℝ≥0∞) * g.edist (e v) (e x) :=
        (hcomp v hv x hxU).2
      _ < (K : ℝ≥0∞) * ENNReal.ofReal r := by
        apply ENNReal.mul_lt_mul_right hKen ENNReal.coe_ne_top
        simpa only [hex, edist, Manifold.riemannianEDist_comm] using
          (show g.edist p (e v) < ENNReal.ofReal r from hy)
      _ = ENNReal.ofReal ((K : ℝ) * r) := by
        rw [ENNReal.ofReal_mul K.coe_nonneg, ENNReal.ofReal_coe_nnreal]
  have hrdiv : r / (K : ℝ) ≤ (K : ℝ) * r := by
    apply (div_le_iff₀ hKpos).mpr
    nlinarith [mul_nonneg hrpos.le (sq_nonneg ((K : ℝ) - 1))]
  have hcover' : Metric.ball (A x) (r / (K : ℝ)) ⊆ ψ '' g.ball p r := by
    intro z hz
    have hzU : A.symm z ∈ U := hlarge z (Metric.ball_subset_ball hrdiv hz)
    refine ⟨f z, ?_, ?_⟩
    · change g.edist p (e (A.symm z)) < ENNReal.ofReal r
      rw [← hex]
      calc
        g.edist (e x) (e (A.symm z)) ≤
            (K : ℝ≥0∞) * EDist.edist (A x) z := by
          simpa only [A.apply_symm_apply] using (hcomp x hxU (A.symm z) hzU).1
        _ < (K : ℝ≥0∞) * ENNReal.ofReal (r / (K : ℝ)) := by
          apply ENNReal.mul_lt_mul_right hKen ENNReal.coe_ne_top
          exact edist_lt_ofReal.mpr (by simpa only [dist_comm] using
            (show dist z (A x) < r / (K : ℝ) from hz))
        _ = ENNReal.ofReal r := by
          rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul K.coe_nonneg,
            mul_div_cancel₀ r hKpos.ne']
    · simp only [ψ, f, Function.comp_apply, e.left_inv (hUe hzU), A.apply_symm_apply]
  have hupper : g.volumeMeasure (g.ball p r) ≤
      (K : ℝ≥0∞) ^ n * volume (Metric.ball (A x) ((K : ℝ) * r)) := by
    change Measure.euclideanHausdorffMeasure n (g.ball p r) ≤ _
    apply (measure_mono hcover).trans
    simpa only [E, EuclideanSpace.euclideanHausdorffMeasure_eq_volume] using
      Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hfLip n
  have hlower : volume (Metric.ball (A x) (r / (K : ℝ))) ≤
      (K : ℝ≥0∞) ^ n * g.volumeMeasure (g.ball p r) := by
    change _ ≤ (K : ℝ≥0∞) ^ n * Measure.euclideanHausdorffMeasure n (g.ball p r)
    rw [← EuclideanSpace.euclideanHausdorffMeasure_eq_volume]
    exact (measure_mono hcover').trans
      (Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hψLip n)
  have hscale (s : ℝ) : volume (Metric.ball (A x) ((K : ℝ) * s)) =
      (K : ℝ≥0∞) ^ n * volume (Metric.ball (0 : E) s) := by
    simpa only [E, finrank_euclideanSpace, Fintype.card_fin, ENNReal.ofReal_pow K.coe_nonneg,
      ENNReal.ofReal_coe_nnreal] using
      Measure.addHaar_ball_mul_of_pos (volume : Measure E) (A x) hKpos s
  constructor
  · rw [hscale, ← mul_assoc, ← pow_add, ← two_mul] at hupper
    exact hupper
  · have hscaled := mul_le_mul_of_nonneg_left hlower (show 0 ≤ (K : ℝ≥0∞) ^ n from zero_le)
    rw [Measure.addHaar_ball_center (volume : Measure E) (A x)] at hscaled
    have heq : (K : ℝ≥0∞) ^ n * volume (Metric.ball (0 : E) (r / (K : ℝ))) =
        volume (Metric.ball (0 : E) r) := by
      rw [← hscale, mul_div_cancel₀ r hKpos.ne',
        Measure.addHaar_ball_center (volume : Measure E) (A x)]
    rwa [heq, ← mul_assoc, ← pow_add, ← two_mul] at hscaled

end PoincareConjecture.RiemannianMetric
