import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Volume.MeasureComparison







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal NNReal

theorem PoincareConjecture.RiemannianMetric.volumeMeasure_image_le_of_tangentNorm_le_on_compact
    {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    [T3Space M] [T3Space N] [MeasurableSpace M] [BorelSpace M]
    [MeasurableSpace N] [BorelSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) N] [IsManifold (𝓡 n) ∞ N]
    (g : PoincareConjecture.RiemannianMetric n M) (h : PoincareConjecture.RiemannianMetric n N)
    {f : M → N} {U s : Set M} (hU : IsOpen U) (hs : IsCompact s) (hsU : s ⊆ U)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) 1 f U)
    {C : ℝ} (hC : 0 < C)
    (hbound : ∀ x ∈ U, ∀ v : TangentSpace (𝓡 n) x,
      h.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x v) ≤ C * g.tangentNorm x v) :
    h.volumeMeasure (f '' s) ≤ ENNReal.ofReal C ^ n * g.volumeMeasure s := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp
  let : Nonempty s := hne.to_subtype
  have hlocal (p : s) : ∃ V : Set M, IsOpen V ∧ (p : M) ∈ V ∧ V ⊆ U ∧
      ∀ x ∈ V, ∀ y ∈ V, h.edist (f x) (f y) ≤ ENNReal.ofReal C * g.edist x y :=
    g.exists_open_edist_image_le_of_tangentNorm_le h (hU.mem_nhds (hsU p.2))
      (fun z hz => hf.contMDiffAt (hU.mem_nhds hz)) hC hbound
  choose V hVo hpV hVU hdist using hlocal
  obtain ⟨a, ha⟩ := hs.isLindelof.indexed_countable_subcover V hVo
    (fun x hx => mem_iUnion.mpr ⟨⟨x,hx⟩, hpV ⟨x,hx⟩⟩)
  let W : ℕ → Set M := fun i => V (a i) ∩ s
  have hWm (i : ℕ) : MeasurableSet (W i) := (hVo _).measurableSet.inter hs.measurableSet
  have hcover : (⋃ i, W i) = s := by
    apply Subset.antisymm (iUnion_subset fun i => inter_subset_right)
    intro x hx
    obtain ⟨i, hi⟩ := mem_iUnion.mp (ha hx)
    exact mem_iUnion.mpr ⟨i, hi, hx⟩
  have hDm (i : ℕ) : MeasurableSet (disjointed W i) := MeasurableSet.disjointed hWm i
  have hD (i : ℕ) : h.volumeMeasure (f '' disjointed W i) ≤
      ENNReal.ofReal C ^ n * g.volumeMeasure (disjointed W i) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 n) M
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨h.toRiemannianMetric⟩
    let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (TangentSpace (𝓡 n) : N → Type _) :=
      ⟨⟨h.inner, h.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
    let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 n) N
    let K : ℝ≥0 := ⟨C,hC.le⟩
    have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq K
    have hLip : LipschitzOnWith K f (disjointed W i) := by
      intro x hx y hy
      change h.edist (f x) (f y) ≤ (K : ℝ≥0∞) * g.edist x y
      rw [hK]
      exact hdist (a i) x ((disjointed_le W i hx).1)
        y ((disjointed_le W i hy).1)
    change Measure.euclideanHausdorffMeasure n (f '' disjointed W i) ≤
      ENNReal.ofReal C ^ n * Measure.euclideanHausdorffMeasure n (disjointed W i)
    simpa only [hK] using
      Poincare.HausdorffDensity.euclideanHausdorffMeasure_image_le hLip n
  have hpartition : (⋃ i, disjointed W i) = s := (iUnion_disjointed).trans hcover
  calc
    h.volumeMeasure (f '' s) = h.volumeMeasure (⋃ i, f '' disjointed W i) := by
      rw [← image_iUnion, hpartition]
    _ ≤ ∑' i, h.volumeMeasure (f '' disjointed W i) := measure_iUnion_le _
    _ ≤ ∑' i, ENNReal.ofReal C ^ n * g.volumeMeasure (disjointed W i) :=
      ENNReal.tsum_le_tsum hD
    _ = ENNReal.ofReal C ^ n * g.volumeMeasure s := by
      rw [ENNReal.tsum_mul_left, ← measure_iUnion (disjoint_disjointed W) hDm, hpartition]
