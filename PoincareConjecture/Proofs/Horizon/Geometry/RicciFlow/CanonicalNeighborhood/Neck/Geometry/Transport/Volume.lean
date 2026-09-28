import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison







noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory Filter
open scoped Manifold ContDiff Bundle ENNReal NNReal Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
  [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
  [SecondCountableTopology M] [MeasurableSpace N] [BorelSpace N]

theorem volumeMeasure_le_image_of_inverse_tangentNorm_le
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (e : OpenPartialHomeomorph M N)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) 1 e.symm e.target)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ z ∈ e.target, ∀ v : TangentSpace (𝓡 n) z,
      g.tangentNorm (e.symm z) (mfderiv (𝓡 n) (𝓡 n) e.symm z v) ≤
        C * h.tangentNorm z v)
    {s : Set M} (hs : MeasurableSet s) (hse : s ⊆ e.source) :
    g.volumeMeasure s ≤ ENNReal.ofReal C ^ n * h.volumeMeasure (e '' s) := by
  let μ := (h.volumeMeasure.restrict e.target).map e.symm
  have hμ : ∀ t : Set M, MeasurableSet t → t ⊆ e.source →
      μ t = h.volumeMeasure (e '' t) := by
    intro t ht hte
    have hm : AEMeasurable e.symm (h.volumeMeasure.restrict e.target) :=
      e.symm.continuousOn.aemeasurable e.open_target.measurableSet
    have hset : e.symm ⁻¹' t ∩ e.target = e '' t := by
      ext y
      constructor
      · intro hy
        exact ⟨e.symm y, hy.1, e.right_inv hy.2⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨by simpa only [mem_preimage, e.left_inv (hte hx)], e.map_source (hte hx)⟩
    dsimp only [μ]
    rw [Measure.map_apply_of_aemeasurable hm ht,
      Measure.restrict_apply' e.open_target.measurableSet, hset]
  rw [← hμ s hs hse]
  change g.volumeMeasure s ≤ (ENNReal.ofReal C ^ n • μ) s
  apply Poincare.HausdorffDensity.measure_le_of_locally_le hs
  intro p hp
  obtain ⟨W, hW, hpW, hWt, hdist⟩ :=
    h.exists_open_edist_image_le_of_tangentNorm_le g
      (e.open_target.mem_nhds (e.map_source (hse hp)))
      (fun z hz ↦ he.contMDiffAt (e.open_target.mem_nhds hz)) hC hbound
  let U := e.source ∩ e ⁻¹' W
  have hU : IsOpen U := e.continuousOn.isOpen_inter_preimage e.open_source hW
  refine ⟨U, hU, ⟨hse hp, hpW⟩, fun t ht hts ↦ ?_⟩
  have hte : t ⊆ e.source := fun x hx ↦ (hts hx).1.1
  change g.volumeMeasure t ≤ ENNReal.ofReal C ^ n * μ t
  rw [hμ t ht hte]
  have him : e.symm '' (e '' t) = t := by
    ext x
    constructor
    · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
      simpa only [e.left_inv (hte hz)] using hz
    · intro hx
      exact ⟨e x, ⟨x, hx, rfl⟩, e.left_inv (hte hx)⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨h.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : N → Type _) :=
    ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
  let K : ℝ≥0 := ⟨C, hC.le⟩
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq K
  have hLip : LipschitzOnWith K e.symm (e '' t) := by
    rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    change g.edist (e.symm (e a)) (e.symm (e b)) ≤
      (K : ℝ≥0∞) * h.edist (e a) (e b)
    rw [hK]
    exact hdist _ (hts ha).1.2 _ (hts hb).1.2
  have hh := Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hLip n
  rw [him] at hh
  change Measure.euclideanHausdorffMeasure n t ≤
    ENNReal.ofReal C ^ n * Measure.euclideanHausdorffMeasure n (e '' t)
  simpa only [hK] using hh

end PoincareConjecture.RiemannianMetric
