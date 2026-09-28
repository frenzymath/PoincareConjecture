import PoincareConjecture.Proofs.M49.RegularLimitDensity
import PoincareConjecture.Proofs.M49.CalibratedLimitVolume
import PoincareConjecture.Proofs.M49.SlabVolume










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M49



theorem event_regular_limit_volume_le_liminf
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants} {P : SurgeryParameters}
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) :
    calibratedMetricVolume E.limit_metric univ ≤
      liminf (fun t => calibratedMetricVolume (E.pre_flow.metric t) univ) (𝓝[<] T) := by
  classical
  rcases isEmpty_or_nonempty E.terminal.carrier with hEmpty | hNonempty
  · let := hEmpty
    rw [univ_eq_empty_iff.mpr hEmpty, measure_empty]
    exact bot_le
  let := hNonempty
  let p := regionOpenPartialHomeomorph E.limit_identify E.regular_limit_open isOpen_univ
  let e0 (y : E.terminal.carrier) :=
    (chartAt (EuclideanSpace ℝ (Fin 3)) (p.symm y)).symm
  let e1 (y : E.terminal.carrier) := (e0 y).trans p
  have hp (y : E.terminal.carrier) : p.symm y ∈ E.regular_limit :=
    p.map_target (mem_univ y)
  have h0 (y : E.terminal.carrier) :
      ContMDiffOn (𝓡 3) (𝓡 3) 1 (e0 y) (e0 y).source := contMDiffOn_chart_symm
  have h0i (y : E.terminal.carrier) :
      ContMDiffOn (𝓡 3) (𝓡 3) 1 (e0 y).symm (e0 y).target := contMDiffOn_chart
  have h1 (y : E.terminal.carrier) :
      ContMDiffOn (𝓡 3) (𝓡 3) 1 (e1 y) (e1 y).source :=
    (E.limit_identify.map_smooth.of_le (by simp)).comp' (h0 y)
  have h1i (y : E.terminal.carrier) :
      ContMDiffOn (𝓡 3) (𝓡 3) 1 (e1 y).symm (e1 y).target :=
    (h0i y).comp' (E.limit_identify.inverse_smooth.of_le (by simp))
  have hy (y : E.terminal.carrier) : y ∈ (e1 y).target :=
    ⟨mem_univ y, mem_chart_source _ _⟩
  obtain ⟨s, hs⟩ := (HereditarilyLindelofSpace.isLindelof
      (univ : Set E.terminal.carrier)).indexed_countable_subcover
    (fun y => (e1 y).target) (fun y => (e1 y).open_target)
    (fun y _ => mem_iUnion.mpr ⟨y, hy y⟩)
  let W : ℕ → Set E.terminal.carrier := fun k => (e1 (s k)).target
  let D := disjointed W
  let C : ℕ → Set (EuclideanSpace ℝ (Fin 3)) :=
    fun k => e1 (s k) ⁻¹' D k ∩ (e1 (s k)).source
  have hDm (k : ℕ) : MeasurableSet (D k) :=
    MeasurableSet.disjointed (fun j => (e1 (s j)).open_target.measurableSet) k
  have hC (k : ℕ) : MeasurableSet (C k) :=
    (e1 (s k)).measurableSet_preimage_inter_source (hDm k)
  have hC1 (k : ℕ) : C k ⊆ (e1 (s k)).source := inter_subset_right
  have hC0 (k : ℕ) : C k ⊆ (e0 (s k)).source :=
    fun _ hx => hx.2.1
  have himage (k : ℕ) : e1 (s k) '' C k = D k := by
    dsimp only [C]
    rw [image_preimage_inter, OpenPartialHomeomorph.image_source_eq_target,
      inter_eq_left.mpr (disjointed_subset W k)]
  have hdis1 : Pairwise (fun i j =>
      Disjoint (e1 (s i) '' C i) (e1 (s j) '' C j)) := by
    simpa only [himage] using disjoint_disjointed W
  have hdis0 : Pairwise (fun i j =>
      Disjoint (e0 (s i) '' C i) (e0 (s j) '' C j)) := by
    intro i j hij
    apply disjoint_left.mpr
    rintro z ⟨x, hx, rfl⟩ ⟨y, hy, heq⟩
    have hi : p (e0 (s i) x) ∈ D i := hx.1
    have hj : p (e0 (s i) x) ∈ D j := by
      rw [← heq]
      exact hy.1
    exact disjoint_left.mp (disjoint_disjointed W hij) hi hj
  have hcover : ⋃ k, e1 (s k) '' C k = univ := by
    simp_rw [himage]
    rw [iUnion_disjointed]
    exact eq_univ_of_univ_subset hs
  apply calibratedVolume_le_liminf_of_chart_cover E.pre_flow.metric E.limit_metric
    (fun k => e0 (s k)) (fun k => e1 (s k))
    (fun k => h0 (s k)) (fun k => h0i (s k))
    (fun k => h1 (s k)) (fun k => h1i (s k)) C hC hC0 hC1 hdis0 hdis1 hcover
  intro k x hx
  have hext : extChartAt (𝓡 3) (p.symm (s k)) =
      (chartAt (EuclideanSpace ℝ (Fin 3)) (p.symm (s k))).toPartialEquiv := by
    ext z <;> simp
  have hxchart : x ∈ (extChartAt (𝓡 3) (p.symm (s k))).target := by
    rw [hext]
    exact hC0 k hx
  have hxU : (extChartAt (𝓡 3) (p.symm (s k))).symm x ∈ E.regular_limit := by
    rw [hext]
    exact hx.2.2
  have hlim := surgeryMetricLimitOn_jacobian_tendsto E.metric_converges
    (hp (s k)) hxchart hxU
  rw [hext] at hlim
  exact hlim



theorem event_regular_limit_volume_le_left_limit
    (H : GeneralizedParabolicRescalingTheory.{u} 3)
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] {L : ℝ≥0∞}
    (hlim : Tendsto (fun t => calibratedMetricVolume (F.metric t) univ)
      (𝓝[F.time_domain ∩ Iio T] T) (𝓝 L)) :
    calibratedMetricVolume (F.event T hT).limit_metric univ ≤ L := by
  let E := F.event T hT
  have hleft : 𝓝[<] T ≤ 𝓝[F.time_domain ∩ Iio T] T := by
    rw [← nhdsWithin_Ico_eq_nhdsLT E.tMinus_lt]
    apply nhdsWithin_mono
    exact fun _ ht => ⟨nonemptyEventPreInterval F T hT ht, ht.2⟩
  have heq : (fun t => calibratedMetricVolume (E.pre_flow.metric t) univ) =ᶠ[𝓝[<] T]
      (fun t => calibratedMetricVolume (F.metric t) univ) := by
    filter_upwards [Ioo_mem_nhdsLT E.tMinus_lt] with t ht
    let rt : Ico E.tMinus T := ⟨t, ⟨ht.1.le, ht.2⟩⟩
    apply (volume_univ_eq_of_metric_isometry H (E.pre_flow.metric t)
      (F.metric t) (E.pre_identify rt) _).symm
    intro x v w
    simpa only [one_mul] using E.pre_metric rt x v w
  have hfixed := (hlim.mono_left hleft).congr' heq.symm
  exact (event_regular_limit_volume_le_liminf E).trans_eq hfixed.liminf_eq

end PoincareConjecture.M49
