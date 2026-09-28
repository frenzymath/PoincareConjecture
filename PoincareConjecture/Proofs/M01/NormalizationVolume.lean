import PoincareConjecture.Definitions.Ch01.Normalization

set_option autoImplicit false

open Bundle Manifold Metric Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal NNReal

universe u

namespace PoincareConjecture

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsManifold I 1 M]

theorem m01_riemannianEDist_symm_extChartAt_le (x : M)
    (hcont : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x))
    {s : Set E}
    (hs : Convex ℝ s) (hsub : s ⊆ (extChartAt I x).target) (C : ℝ≥0)
    (hC : ∀ z ∈ s,
      letI := normedAddCommGroupTangentSpaceVectorSpace z
      letI := normedSpaceTangentSpaceVectorSpace z
      letI : SeminormedAddCommGroup
          (TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I ((extChartAt I x).symm z)) :=
        ContinuousLinearMap.toSeminormedAddCommGroup
      ‖mfderiv[range I] (extChartAt I x).symm z‖ₑ ≤ C)
    {a b : E} (ha : a ∈ s) (hb : b ∈ s) :
    riemannianEDist I ((extChartAt I x).symm a) ((extChartAt I x).symm b) ≤
      C * edist a b := by
  let := hcont
  let (z : E) : NormedAddCommGroup (TangentSpace 𝓘(ℝ, E) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : E) : NormedSpace ℝ (TangentSpace 𝓘(ℝ, E) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let (z : E) (y : M) : SeminormedAddCommGroup
      (TangentSpace 𝓘(ℝ, E) z →L[ℝ] TangentSpace I y) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let η := ContinuousAffineMap.lineMap (R := ℝ) a b
  let γ := (extChartAt I x).symm ∘ η
  have hη : Icc 0 1 ⊆ ⇑η ⁻¹' s := by
    simp only [← image_subset_iff, ContinuousAffineMap.coe_lineMap_eq,
      ← segment_eq_image_lineMap, η]
    exact hs.segment_subset ha hb
  have htarget := hη.trans (preimage_mono hsub)
  have η_smooth : CMDiff[Icc 0 1] 1 η := by
    apply ContMDiff.contMDiffOn
    rw [contMDiff_iff_contDiff]
    exact ContinuousAffineMap.contDiff _
  have hlength : riemannianEDist I ((extChartAt I x).symm a)
      ((extChartAt I x).symm b) ≤ pathELength I γ 0 1 := by
    apply riemannianEDist_le_pathELength _ _ _ zero_le_one
    · exact (contMDiffOn_extChartAt_symm x).comp η_smooth htarget
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
    · simp [γ, η, ContinuousAffineMap.coe_lineMap_eq]
  apply hlength.trans
  rw [← lintegral_fderiv_lineMap_eq_edist, pathELength_eq_lintegral_mfderivWithin_Icc,
    ← lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  apply setLIntegral_mono' measurableSet_Icc (fun t ht ↦ ?_)
  have hderiv : mfderiv[Icc 0 1] γ t =
      (mfderiv[range I] (extChartAt I x).symm (η t)) ∘L (mfderiv[Icc 0 1] η t) := by
    apply mfderivWithin_comp
    · exact mdifferentiableWithinAt_extChartAt_symm (htarget ht)
    · exact η_smooth.mdifferentiableOn one_ne_zero t ht
    · exact htarget.trans (preimage_mono (extChartAt_target_subset_range x))
    · rw [uniqueMDiffWithinAt_iff_uniqueDiffWithinAt]
      exact uniqueDiffOn_Icc zero_lt_one t ht
  have happly : mfderiv[Icc 0 1] γ t 1 =
      (mfderiv[range I] (extChartAt I x).symm (η t)) (mfderiv[Icc 0 1] η t 1) :=
    congr($hderiv 1)
  rw [happly]
  apply (ContinuousLinearMap.le_opENorm _ _).trans
  gcongr
  · exact hC _ (hη ht)
  · simp only [mfderivWithin_eq_fderivWithin]
    exact le_rfl

end

section

variable {M : Type u} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

theorem m01_euclideanHausdorff_locallyFinite :
    IsLocallyFiniteMeasure
      (Measure.hausdorffMeasure (3 : ℝ) : Measure (EuclideanSpace ℝ (Fin 3))) := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [← hdim]
  infer_instance

theorem m01_euclideanHausdorff_unitBall_pos :
    0 < euclideanUnitBallHausdorffVolume := by
  have hdim : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  unfold euclideanUnitBallHausdorffVolume
  rw [← hdim]
  exact isOpen_ball.measure_pos _ (Metric.nonempty_ball.mpr zero_lt_one)

theorem m01_euclideanHausdorffCalibration_lt_top : euclideanHausdorffCalibration < ⊤ := by
  apply ENNReal.div_lt_top
  · exact Metric.isBounded_ball.measure_lt_top.ne
  · exact m01_euclideanHausdorff_unitBall_pos.ne'

theorem m01_hausdorffVolume_finite [CompactSpace M] (g : RiemannianMetric 3 M) :
    g.hausdorffVolume Set.univ < ⊤ := by
  let (z : EuclideanSpace ℝ (Fin 3)) :
      NormedAddCommGroup (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) z) :=
    normedAddCommGroupTangentSpaceVectorSpace z
  let (z : EuclideanSpace ℝ (Fin 3)) :
      NormedSpace ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) z) :=
    normedSpaceTangentSpaceVectorSpace z
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let (z : EuclideanSpace ℝ (Fin 3)) (y : M) :
      SeminormedAddCommGroup
        (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) z →L[ℝ] TangentSpace (𝓡 3) y) :=
    ContinuousLinearMap.toSeminormedAddCommGroup
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  let := m01_euclideanHausdorff_locallyFinite
  change Measure.hausdorffMeasure (3 : ℝ) (Set.univ : Set M) < ⊤
  apply isCompact_univ.measure_lt_top_of_nhdsWithin
  intro x _
  rw [nhdsWithin_univ]
  obtain ⟨C, _, hC⟩ := eventually_enorm_mfderivWithin_symm_extChartAt_lt (𝓡 3) x
  simp only [ModelWithCorners.range_eq_univ, nhdsWithin_univ] at hC
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (extChartAt_target_mem_nhds (I := 𝓡 3) x) hC)
  let e := extChartAt (𝓡 3) x
  have htarget : Metric.ball (e x) r ⊆ e.target := fun y hy => (hball hy).1
  have hLip : LipschitzOnWith C e.symm (Metric.ball (e x) r) := by
    intro a ha b hb
    exact m01_riemannianEDist_symm_extChartAt_le x (hcont := inferInstance)
      (convex_ball _ _) htarget C
      (fun z hz => by
        simpa only [ModelWithCorners.range_eq_univ] using (hball hz).2.le) ha hb
  refine ⟨e.symm '' Metric.ball (e x) r, ?_, ?_⟩
  · apply mem_of_superset (inter_mem (extChartAt_source_mem_nhds (I := 𝓡 3) x)
      ((continuousAt_extChartAt (I := 𝓡 3) x).preimage_mem_nhds (ball_mem_nhds _ hr)))
    intro y hy
    exact ⟨e y, hy.2, e.left_inv hy.1⟩
  · apply (hLip.hausdorffMeasure_image_le (d := 3) (by norm_num)).trans_lt
    rw [show (3 : ℝ) = (3 : ℕ) by norm_num, ENNReal.rpow_natCast]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.coe_lt_top)
      Metric.isBounded_ball.measure_lt_top

theorem m01_normalizedMetricVolume_finite [CompactSpace M] (g : RiemannianMetric 3 M) :
    normalizedMetricVolume g Set.univ < ⊤ := by
  change (euclideanHausdorffCalibration • g.hausdorffVolume) Set.univ < ⊤
  rw [Measure.smul_apply, smul_eq_mul]
  exact ENNReal.mul_lt_top m01_euclideanHausdorffCalibration_lt_top
    (m01_hausdorffVolume_finite g)

end

end PoincareConjecture
