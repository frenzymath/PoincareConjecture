import PoincareConjecture.Proofs.M49.SlabVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Evolution.VolumeEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Volume.Surgery.Event.EventHistory
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Rescaling.Theory

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.SurgeryVolume

theorem pinched_scalar_ge_neg_six {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [T2Space M] [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [SecondCountableTopology M] {g : RiemannianMetric 3 M}
    {D : LeviCivitaData g} {t : ℝ} (ht : SurgeryPinchedAt D t) (x : M) :
    -6 ≤ D.scalarCurvature x := by
  have hd : 0 < 1 + 4 * t := by linarith [ht.1]
  apply le_trans _ (ht.2.1 x (mem_univ x))
  apply (le_div_iff₀ hd).mpr
  nlinarith [ht.1]

theorem volume_univ_eq_of_metric_isometry {n : ℕ}
    (H : GeneralizedParabolicRescalingTheory.{u} n)
    {M N : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [MeasurableSpace M] [BorelSpace M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
    [IsManifold (𝓡 n) ∞ N] [T3Space N] [MeasurableSpace N] [BorelSpace N]
    (g : RiemannianMetric n M) (h : RiemannianMetric n N)
    (f : Diffeomorph (𝓡 n) (𝓡 n) M N ∞) (hf : MetricHomothety g h f 1) :
    calibratedMetricVolume h univ = calibratedMetricVolume g univ := by
  have he := (H.metric_homothety M N g h f 1 (by norm_num) hf).volume_image univ
  change calibratedMetricVolume h (f '' univ) =
    ENNReal.ofReal ((1 : ℝ) ^ ((n : ℝ) / 2)) * calibratedMetricVolume g univ at he
  rw [image_univ_of_surjective (f := (f : M → N)) f.surjective, Real.one_rpow,
    ENNReal.ofReal_one, one_mul] at he
  exact he

theorem regularSlab_volume_le_exp_mul (H : GeneralizedParabolicRescalingTheory.{u} 3)
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
    intro x v w
    simpa only [one_mul] using B.metric_pullback r x v w
  have hvol (r : Icc a b) := volume_univ_eq_of_metric_isometry H
    (B.flow.metric r.1) (metric r.1) (B.identify r) (hiso r)
  rw [hvol ⟨t, ht⟩, hvol ⟨s, hs⟩]
  apply calibratedMetricVolume_le_exp_mul B.flow hst
    (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩) _ MeasurableSet.univ
  intro r hr x
  let rt : Icc a b := ⟨r, ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩⟩
  have he := (H.metric_homothety (slice a).carrier (slice r).carrier
    (B.flow.metric r) (metric r) (B.identify rt) 1 (by norm_num) (hiso rt)).scalar_eq
      (B.flow.connection r) (connection r) x
  rw [div_one] at he
  rw [← he]
  exact pinched_scalar_ge_neg_six (hpinched r rt.2) _

theorem regular_volume_le_exp_mul (H : GeneralizedParabolicRescalingTheory.{u} 3)
    (F : SurgeryFlowData.{u}) {a b : ℝ} (hab : a ≤ b)
    (hJ : Icc a b ⊆ F.time_domain) (hevents : Disjoint F.surgery_times (Ioc a b))
    (hpinched : ∀ t ∈ Icc a b, SurgeryPinchedAt (F.connection t) t) :
    calibratedMetricVolume (F.metric b) univ ≤
      ENNReal.ofReal (Real.exp (6 * (b - a))) * calibratedMetricVolume (F.metric a) univ := by
  obtain hlt | rfl := hab.lt_or_eq
  · exact regularSlab_volume_le_exp_mul H F.connection
      (F.regular_slabs a b hlt hJ hevents) hpinched ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab
  · simp

theorem preEvent_volume_le_exp_mul (H : GeneralizedParabolicRescalingTheory.{u} 3)
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
    intro x v w
    simpa only [one_mul] using E.pre_metric r x v w
  have hvol (r : Ico E.tMinus T) := volume_univ_eq_of_metric_isometry H
    (E.pre_flow.metric r.1) (F.metric r.1) (E.pre_identify r) (hiso r)
  rw [hvol ⟨t, ht⟩, hvol ⟨s, hs⟩]
  apply calibratedMetricVolume_le_exp_mul E.pre_flow hst
    (fun r hr => ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩) _ MeasurableSet.univ
  intro r hr x
  let rt : Ico E.tMinus T := ⟨r, ⟨hs.1.trans hr.1, hr.2.trans_lt ht.2⟩⟩
  have he := (H.metric_homothety (F.slice E.tMinus).carrier (F.slice r).carrier
    (E.pre_flow.metric r) (F.metric r) (E.pre_identify rt) 1 (by norm_num) (hiso rt)).scalar_eq
      (E.pre_flow.connection r) (F.connection r) x
  rw [div_one] at he
  rw [← he]
  exact pinched_scalar_ge_neg_six (hpinched r rt.2) _

end PoincareConjecture.SurgeryVolume
