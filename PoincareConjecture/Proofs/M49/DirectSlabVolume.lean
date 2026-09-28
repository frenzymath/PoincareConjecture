import PoincareConjecture.Proofs.M49.SlabVolume
import PoincareConjecture.Proofs.M49.LocalIsometryVolume
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u v

namespace PoincareConjecture.M49



theorem volume_univ_eq_of_metric_isometry_direct {n : ℕ}
    {M : Type u} {N : Type v} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M] [SecondCountableTopology M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (hf : MetricHomothety g h f 1) :
    calibratedMetricVolume h univ = calibratedMetricVolume g univ := by
  have he := calibratedMetricVolume_image_eq_of_injective_isometry g h
    (f := (f : M → N)) f.contMDiff f.injective
    (fun x a b => by simpa only [one_mul] using hf x a b) MeasurableSet.univ
  simpa only [image_univ_of_surjective (f := (f : M → N)) f.surjective] using he



theorem regularSlab_volume_le_exp_mul_direct
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier}
    (connection : ∀ t, LeviCivitaData (metric t)) {a b : ℝ}
    (B : SurgeryRegularSlab slice metric a b)
    (hpinched : ∀ t ∈ Icc a b, SurgeryPinchedAt (connection t) t)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    calibratedMetricVolume (metric t) univ ≤
      ENNReal.ofReal (Real.exp (6 * (t - s))) * calibratedMetricVolume (metric s) univ := by
  have hiso (r : Icc a b) :
      MetricHomothety (B.flow.metric r.1) (metric r.1) (B.identify r) 1 := by
    intro x a b
    simpa only [one_mul] using B.metric_pullback r x a b
  have hvol (r : Icc a b) := volume_univ_eq_of_metric_isometry_direct
    (B.flow.metric r.1) (metric r.1) (B.identify r) (hiso r)
  rw [hvol ⟨t, ht⟩, hvol ⟨s, hs⟩]
  apply calibratedMetricVolume_le_exp_mul B.flow hst
    (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩) _ MeasurableSet.univ
  intro r hr x
  let rt : Icc a b := ⟨r, ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩⟩
  have he := (B.flow.connection r).scalarCurvature_eq_of_local_isometry (connection r)
    isOpen_univ (B.identify rt).contMDiff.contMDiffOn
    (fun y _ a b => (B.metric_pullback rt y a b).symm) (mem_univ x)
  rw [he]
  exact pinched_scalar_ge_neg_six (hpinched r rt.2) _



theorem regular_volume_le_exp_mul_direct
    (F : SurgeryFlowData.{u}) {a b : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ F.time_domain) (hevents : Disjoint F.surgery_times (Ioc a b))
    (hpinched : ∀ t ∈ Icc a b, SurgeryPinchedAt (F.connection t) t) :
    calibratedMetricVolume (F.metric b) univ ≤
      ENNReal.ofReal (Real.exp (6 * (b - a))) * calibratedMetricVolume (F.metric a) univ := by
  obtain hlt | rfl := hab.lt_or_eq
  · exact regularSlab_volume_le_exp_mul_direct F.connection
      (F.regular_slabs a b hlt hJ hevents) hpinched ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  · simp



theorem preEvent_volume_le_exp_mul_direct
    (F : SurgeryFlowData.{u}) (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier]
    (hpinched : ∀ t ∈ Ico (F.event T hT).tMinus T, SurgeryPinchedAt (F.connection t) t)
    {s t : ℝ} (hs : s ∈ Ico (F.event T hT).tMinus T)
    (ht : t ∈ Ico (F.event T hT).tMinus T) (hst : s ≤ t) :
    calibratedMetricVolume (F.metric t) univ ≤
      ENNReal.ofReal (Real.exp (6 * (t - s))) * calibratedMetricVolume (F.metric s) univ := by
  let E := F.event T hT
  have hiso (r : Ico E.tMinus T) :
      MetricHomothety (E.pre_flow.metric r.1) (F.metric r.1) (E.pre_identify r) 1 := by
    intro x a b
    simpa only [one_mul] using E.pre_metric r x a b
  have hvol (r : Ico E.tMinus T) := volume_univ_eq_of_metric_isometry_direct
    (E.pre_flow.metric r.1) (F.metric r.1) (E.pre_identify r) (hiso r)
  rw [hvol ⟨t, ht⟩, hvol ⟨s, hs⟩]
  apply calibratedMetricVolume_le_exp_mul E.pre_flow hst
    (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩) _ MeasurableSet.univ
  intro r hr x
  let rt : Ico E.tMinus T := ⟨r, ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩⟩
  have he := (E.pre_flow.connection r).scalarCurvature_eq_of_local_isometry (F.connection r)
    isOpen_univ (E.pre_identify rt).contMDiff.contMDiffOn
    (fun y _ a b => (E.pre_metric rt y a b).symm) (mem_univ x)
  rw [he]
  exact pinched_scalar_ge_neg_six (hpinched r rt.2) _

end PoincareConjecture.M49
