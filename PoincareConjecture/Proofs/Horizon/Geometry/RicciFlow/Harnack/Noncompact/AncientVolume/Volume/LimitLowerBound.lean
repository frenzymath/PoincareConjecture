import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.Splitting.CompleteCoverage
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Balls

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology Bundle ENNReal

private theorem euclideanHausdorffMeasure_le_mul_image
    {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {C : NNReal} (hf : AntilipschitzWith C f) (n : ℕ) (s : Set X) :
    Measure.euclideanHausdorffMeasure n s ≤
      (C : ℝ≥0∞) ^ n * Measure.euclideanHausdorffMeasure n (f '' s) := by
  have h := hf.le_hausdorffMeasure_image (Nat.cast_nonneg n : (0 : ℝ) ≤ n) s
  rw [ENNReal.rpow_natCast] at h
  simp only [Measure.euclideanHausdorffMeasure_def, Measure.smul_apply,
    ENNReal.smul_def, smul_eq_mul]
  exact (mul_le_mul_right h _).trans_eq (by ac_rfl)

private theorem euclideanHausdorffMeasure_ball_le_of_distortion
    {X Y : Type*} [EMetricSpace X] [EMetricSpace Y]
    [MeasurableSpace X] [BorelSpace X] [MeasurableSpace Y] [BorelSpace Y]
    (n : ℕ) (f : X → Y) (p : X) (q : Y) {A C : ℝ}
    (hA : 0 < A) (hC : 0 < C) (hp : f p = q)
    (hbound : ∀ x ∈ Metric.eball p (ENNReal.ofReal A),
      ∀ y ∈ Metric.eball p (ENNReal.ofReal A),
      edist (f x) (f y) ≤ ENNReal.ofReal C * edist x y ∧
        edist x y ≤ ENNReal.ofReal C * edist (f x) (f y)) :
    Measure.euclideanHausdorffMeasure n (Metric.eball p (ENNReal.ofReal A)) ≤
      ENNReal.ofReal C ^ n *
        Measure.euclideanHausdorffMeasure n (Metric.eball q (ENNReal.ofReal (C * A))) := by
  let B := Metric.eball p (ENNReal.ofReal A)
  let F : B → Y := fun x => f x.val
  let Cn : NNReal := ⟨C, hC.le⟩
  have hcoe : (Cn : ℝ≥0∞) = ENNReal.ofReal C := ENNReal.coe_nnreal_eq Cn
  have hanti : AntilipschitzWith Cn F := by
    intro x y
    change edist x.val y.val ≤ (Cn : ℝ≥0∞) *
      edist (f x.val) (f y.val)
    rw [hcoe]
    exact (hbound x.val x.property y.val y.property).2
  have himage : F '' (univ : Set B) ⊆ Metric.eball q (ENNReal.ofReal (C * A)) := by
    rintro z ⟨x, _, rfl⟩
    have hmem : p ∈ B := Metric.mem_eball_self (ENNReal.ofReal_pos.mpr hA)
    have h := (hbound x.val x.property p hmem).1
    rw [hp] at h
    apply h.trans_lt
    rw [ENNReal.ofReal_mul hC.le]
    exact (ENNReal.mul_lt_mul_right (ENNReal.ofReal_pos.mpr hC).ne'
      ENNReal.ofReal_ne_top) x.property
  have h := euclideanHausdorffMeasure_le_mul_image hanti n univ
  have hsource : Measure.euclideanHausdorffMeasure n (univ : Set B) =
      Measure.euclideanHausdorffMeasure n B := by
    simpa only [Subtype.range_coe, image_univ] using
      (isometry_subtype_coe.euclideanHausdorffMeasure_image (univ : Set B)).symm
  rw [hsource] at h
  rw [hcoe] at h
  exact h.trans (mul_le_mul_right (measure_mono himage) _)

namespace PoincareConjecture.FlowCarrier

noncomputable def metricRiemannianVolume {n : ℕ} (C : FlowCarrier n) (g : C.metric) :
    @Measure C.carrier C.measurableSpace :=
  letI : TopologicalSpace C.carrier := C.topologicalSpace
  letI : MeasurableSpace C.carrier := C.measurableSpace
  letI : BorelSpace C.carrier := C.borelSpace
  letI : ChartedSpace (EuclideanSpace ℝ (Fin n)) C.carrier := C.chartedSpace
  letI : IsManifold (𝓡 n) ∞ C.carrier := C.isManifold
  letI : T3Space C.carrier := C.t3Space
  g.volumeMeasure

end PoincareConjecture.FlowCarrier

namespace PoincareConjecture.PointedGeometricConvergence

variable {n : ℕ} {T' T : ℝ} {S : PointedFlowSequence n T' T}

theorem eventually_source_ball_volume_le_of_metricComplete_zero
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    {A C : ℝ} (hA : 0 < A) (hC : 1 < C) (hC2 : C < 2) :
    ∀ᶠ k in atTop,
      (S.carrier (G.subsequence k)).metricRiemannianVolume
          ((S.flow (G.subsequence k)).metricAt 0) ((S.flow (G.subsequence k)).zeroBall A) ≤
        ENNReal.ofReal C ^ n * G.limitCarrier.metricRiemannianVolume
          (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall (C * A)) := by
  have hcover := G.source_ball_coverage_of_metricComplete_zero hT hcomplete
  filter_upwards [G.eventually_inverse_edist_bounds_of_source_ball_coverage
    hT hcover hA hC hC2] with k hk
  let : TopologicalSpace G.limitCarrier.carrier := G.limitCarrier.topologicalSpace
  let : MeasurableSpace G.limitCarrier.carrier := G.limitCarrier.measurableSpace
  let : BorelSpace G.limitCarrier.carrier := G.limitCarrier.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) G.limitCarrier.carrier := G.limitCarrier.chartedSpace
  let : IsManifold (𝓡 n) ∞ G.limitCarrier.carrier := G.limitCarrier.isManifold
  let : EMetricSpace G.limitCarrier.carrier :=
    G.limitCarrier.metricEMetricSpace (G.limitFlow.metricAt 0)
  let : BorelSpace G.limitCarrier.carrier := G.limitCarrier.borelSpace
  let Q := S.carrier (G.subsequence k)
  let : TopologicalSpace Q.carrier := Q.topologicalSpace
  let : MeasurableSpace Q.carrier := Q.measurableSpace
  let : BorelSpace Q.carrier := Q.borelSpace
  let : ChartedSpace (EuclideanSpace ℝ (Fin n)) Q.carrier := Q.chartedSpace
  let : IsManifold (𝓡 n) ∞ Q.carrier := Q.isManifold
  let : EMetricSpace Q.carrier := Q.metricEMetricSpace ((S.flow (G.subsequence k)).metricAt 0)
  let : BorelSpace Q.carrier := Q.borelSpace
  let inv := fun z => ((G.embedding k).inverse (0, z)).2
  have hbase : inv (S.flow (G.subsequence k)).base = G.limitFlow.base := by
    rw [show (S.flow (G.subsequence k)).base =
      ((G.embedding k).toFun (0, G.limitFlow.base)).2 from
        (congrArg Prod.snd (G.base_preserving k)).symm]
    exact (G.embedding k).spatialInverse_comp_spatialMap hT (G.base_in_exhaustion k)
  have hsourceBall : (S.flow (G.subsequence k)).zeroBall A =
      Metric.eball (S.flow (G.subsequence k)).base (ENNReal.ofReal A) := by
    ext x
    change edist (S.flow (G.subsequence k)).base x < ENNReal.ofReal A ↔
      edist x (S.flow (G.subsequence k)).base < ENNReal.ofReal A
    rw [edist_comm]
  have hlimitBall : G.limitFlow.zeroBall (C * A) =
      Metric.eball G.limitFlow.base (ENNReal.ofReal (C * A)) := by
    ext x
    change edist G.limitFlow.base x < ENNReal.ofReal (C * A) ↔
      edist x G.limitFlow.base < ENNReal.ofReal (C * A)
    rw [edist_comm]
  change Measure.euclideanHausdorffMeasure n ((S.flow (G.subsequence k)).zeroBall A) ≤
    ENNReal.ofReal C ^ n * Measure.euclideanHausdorffMeasure n (G.limitFlow.zeroBall (C * A))
  rw [hsourceBall, hlimitBall]
  apply euclideanHausdorffMeasure_ball_le_of_distortion n inv _ _ hA
    (zero_lt_one.trans hC) hbase
  simpa only [hsourceBall] using hk

theorem ball_volume_lower_bound_of_metricComplete_zero
    (G : PointedGeometricConvergence S) (hT : T' < 0 ∧ 0 < T)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metricAt 0))
    (v : ℝ)
    (hvolume : ∀ A : ℝ, 0 < A → ∀ᶠ k in atTop,
      ENNReal.ofReal (v * A ^ n) ≤
        (S.carrier (G.subsequence k)).metricRiemannianVolume
          ((S.flow (G.subsequence k)).metricAt 0) ((S.flow (G.subsequence k)).zeroBall A)) :
    ∀ R : ℝ, 0 < R → ENNReal.ofReal (v * R ^ n) ≤
      G.limitCarrier.metricRiemannianVolume
        (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R) := by
  intro R hR
  let V := G.limitCarrier.metricRiemannianVolume
    (G.limitFlow.metricAt 0) (G.limitFlow.zeroBall R)
  have hbound (C : ℝ) (hC : 1 < C) (hC2 : C < 2) :
      ENNReal.ofReal (v * (R / C) ^ n) ≤ ENNReal.ofReal C ^ n * V := by
    have hC0 := zero_lt_one.trans hC
    have hA : 0 < R / C := div_pos hR hC0
    obtain ⟨k, hkvolume, hkbound⟩ :=
      ((hvolume (R / C) hA).and
        (G.eventually_source_ball_volume_le_of_metricComplete_zero hT hcomplete hA hC hC2)).exists
    have heq : C * (R / C) = R := mul_div_cancel₀ R hC0.ne'
    exact hkvolume.trans (by simpa only [heq] using hkbound)
  have hleft : Tendsto (fun C : ℝ => ENNReal.ofReal (v * (R / C) ^ n))
      (𝓝[>] (1 : ℝ)) (𝓝 (ENNReal.ofReal (v * R ^ n))) := by
    have hreal : Tendsto (fun C : ℝ => v * (R / C) ^ n)
        (𝓝[>] (1 : ℝ)) (𝓝 (v * R ^ n)) := by
      have hid : Tendsto (fun C : ℝ => C) (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ)) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [div_one, Pi.div_apply] using (tendsto_const_nhds (x := v)).mul
        (((tendsto_const_nhds (x := R)).div hid (one_ne_zero : (1 : ℝ) ≠ 0)).pow n)
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp hreal
  have hfactor : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n)
      (𝓝[>] (1 : ℝ)) (𝓝 (1 : ℝ≥0∞)) := by
    simpa only [ENNReal.ofReal_one, one_pow] using
      ENNReal.Tendsto.pow (n := n)
        ((ENNReal.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds)
  have hright : Tendsto (fun C : ℝ => ENNReal.ofReal C ^ n * V)
      (𝓝[>] (1 : ℝ)) (𝓝 V) := by
    simpa only [one_mul] using ENNReal.Tendsto.mul hfactor (Or.inl one_ne_zero)
      tendsto_const_nhds (Or.inr ENNReal.one_ne_top)
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)).filter_mono nhdsWithin_le_nhds]
    with C hC hC2
  exact hbound C hC hC2

end PoincareConjecture.PointedGeometricConvergence
