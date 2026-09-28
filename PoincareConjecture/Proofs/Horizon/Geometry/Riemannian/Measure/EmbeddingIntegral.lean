import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.SpatialEmbedding

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [MeasurableSpace N] [BorelSpace N]

theorem lintegral_image_le_of_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) {V : Set M} (hV : IsOpen V)
    (hVe : V ⊆ e.source)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ V, ∀ v : TangentSpace (𝓡 n) z,
      h.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v) ≤ C * g.tangentNorm z v)
    {F : N → ℝ≥0∞} (hF : ContinuousOn F e.target) :
    (∫⁻ y in e '' V, F y ∂h.volumeMeasure) ≤
      ENNReal.ofReal C ^ n * ∫⁻ x in V, F (e x) ∂g.volumeMeasure := by
  classical
  let μ := (h.volumeMeasure.restrict e.target).map e.symm
  have hm : AEMeasurable e.symm (h.volumeMeasure.restrict e.target) :=
    e.symm.continuousOn.aemeasurable e.open_target.measurableSet
  have hμ (s : Set M) (hs : MeasurableSet s) (hse : s ⊆ e.source) :
      μ s = h.volumeMeasure (e '' s) := by
    have hset : e.symm ⁻¹' s ∩ e.target = e '' s := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy.1, e.right_inv hy.2⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨by simpa only [mem_preimage, e.left_inv (hse hx)], e.map_source (hse hx)⟩
    dsimp only [μ]
    rw [Measure.map_apply_of_aemeasurable hm hs,
      Measure.restrict_apply' e.open_target.measurableSet, hset]
  have hμV : μ.restrict V ≤ ENNReal.ofReal C ^ n • g.volumeMeasure.restrict V := by
    apply Measure.le_iff.mpr
    intro s hs
    rw [Measure.restrict_apply hs, Measure.smul_apply, Measure.restrict_apply hs]
    rw [hμ (s ∩ V) (hs.inter hV.measurableSet) (inter_subset_right.trans hVe)]
    exact g.volumeMeasure_image_le_of_tangentNorm_le h e hV hVe he hC hbound
      (hs.inter hV.measurableSet) inter_subset_right
  have hcomp : ContinuousOn (fun x => F (e x)) V :=
    hF.comp (e.continuousOn.mono hVe) (fun _ hx => e.map_source (hVe hx))
  have hi : Measurable (V.indicator (fun x => F (e x))) :=
    hcomp.measurable_piecewise continuousOn_const hV.measurableSet
  have htransport : (∫⁻ x in V, F (e x) ∂μ) = ∫⁻ y in e '' V, F y ∂h.volumeMeasure := by
    rw [← lintegral_indicator hV.measurableSet]
    rw [show μ = (h.volumeMeasure.restrict e.target).map e.symm from rfl,
      lintegral_map' hi.aemeasurable hm]
    have heV : IsOpen (e '' V) := e.isOpen_image_of_subset_source hV hVe
    rw [← Measure.restrict_restrict_of_subset (show e '' V ⊆ e.target from by
      rintro _ ⟨x, hx, rfl⟩
      exact e.map_source (hVe hx))]
    rw [← lintegral_indicator heV.measurableSet]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem e.open_target.measurableSet] with y hy
    by_cases hmem : e.symm y ∈ V
    · have him : y ∈ e '' V := ⟨e.symm y, hmem, e.right_inv hy⟩
      simp only [indicator_of_mem hmem, indicator_of_mem him, e.right_inv hy]
    · have him : y ∉ e '' V := by
        rintro ⟨x, hx, rfl⟩
        exact hmem (by rwa [e.left_inv (hVe hx)])
      simp only [indicator_of_notMem hmem, indicator_of_notMem him]
  rw [← htransport]
  exact (lintegral_mono' hμV le_rfl).trans_eq (by
    rw [lintegral_smul_measure, smul_eq_mul])

omit [SecondCountableTopology M] in
theorem lintegral_le_image_of_tangentNorm_le [SecondCountableTopology N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N) {V : Set M} (hV : IsOpen V)
    (hVe : V ⊆ e.source)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ V, ∀ v : TangentSpace (𝓡 n) z,
      g.tangentNorm z v ≤ C * h.tangentNorm (e z) (mfderiv (𝓡 n) (𝓡 n) e z v))
    {F : N → ℝ≥0∞} (hF : ContinuousOn F e.target) :
    (∫⁻ x in V, F (e x) ∂g.volumeMeasure) ≤
      ENNReal.ofReal C ^ n * ∫⁻ y in e '' V, F y ∂h.volumeMeasure := by
  have hD : e.MDifferentiable (𝓡 n) (𝓡 n) :=
    ⟨he.mdifferentiableOn one_ne_zero, hei.mdifferentiableOn one_ne_zero⟩
  have hinv := g.inverse_tangentNorm_le_of_le h e hD hVe hbound
  have hback : e.symm '' (e '' V) = V := by
    rw [image_image]
    exact Set.EqOn.image_eq_self (fun x hx => e.left_inv (hVe hx))
  have h := h.lintegral_image_le_of_tangentNorm_le g e.symm
    (e.isOpen_image_of_subset_source hV hVe)
    (by rintro _ ⟨x, hx, rfl⟩; exact e.map_source (hVe hx)) hei hC hinv
    (hF.comp e.continuousOn e.mapsTo)
  rw [hback] at h
  refine h.trans_eq (congrArg (fun z => ENNReal.ofReal C ^ n * z) ?_)
  apply setLIntegral_congr_fun (e.isOpen_image_of_subset_source hV hVe).measurableSet
  rintro _ ⟨x, hx, rfl⟩
  dsimp only [Function.comp_apply]
  rw [e.left_inv (hVe hx)]

end PoincareConjecture.RiemannianMetric
