import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_InitialCapture
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_HistoryComparison
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricComparison
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.Prop16_4_RegularRegion
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Lemma16_8_InitialChartBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12



noncomputable def safeTestInterval (a : ℝ) (ha : 0 < a) : SpacetimeInterval where
  domain := Icc (-a) 0
  ordConnected := ordConnected_Icc
  nontrivial := ⟨-a, ⟨le_rfl, by linarith⟩, 0, ⟨by linarith, le_rfl⟩, by linarith⟩



structure TestedSafeCylinder
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {D : NoncollapseTest F O} (H : HalfRadiusHistory D) (rho a : ℝ) (ha : 0 < a) where
  source : TopologicalSpace.Opens (F.slice D.time).carrier
  source_eq : (source : Set (F.slice D.time).carrier) =
    (F.metric D.time).ball D.center (rho / 2)
  center_mem : D.center ∈ source
  cylinder : GeneralizedFlowCylinder H.spacetime.history.generalized (F.slice D.time)
    D.time 1 (safeTestInterval a ha).domain source
  time_subset : (cylinderPhysicalInterval D.time 1 cylinder.scale_pos
    (safeTestInterval a ha)).domain ⊆ H.spacetime.history.generalized.interval
  physical_eq : (cylinderPhysicalInterval D.time 1 cylinder.scale_pos
    (safeTestInterval a ha)).domain = Icc (D.time - a) D.time
  based : ∀ hzero, cylinder.pointMap 0 hzero D.center =
    ((H.spacetime.geometry.sliceIdentification D.time).identification H.center).val
  metric_lower : ∀ s hs (z : source) (v : TangentSpace (𝓡 3) z.val),
    (1 / 2 : ℝ) * (F.metric D.time).inner z.val v v ≤ cylinder.pullbackInner s hs z.val v v
  scalar_upper : ∀ w : (H.spacetime.geometry.realization.timeIntervals.interval
      (cylinderPhysicalInterval D.time 1 cylinder.scale_pos (safeTestInterval a ha))).Point ×
        source,
    horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
      (rawCylinderMap H.spacetime.geometry.realization cylinder w) ≤ 9 * rho⁻¹ ^ 2

private theorem test_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))




theorem exists_testedSafeCylinder
    (P : M46Predecessors.{u}) (P44 : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (D : NoncollapseTest F O) (H : HalfRadiusHistory D) (hpinch : SurgeryFlowPinched F)
    {rho a : ℝ} (hrho : 0 < rho) (hradius : rho ≤ D.radius) (ha : 0 < a)
    (hatime : a ≤ rho ^ 2 / 4) (hametric : a ≤ rho ^ 2 / 12) :
    Nonempty (TestedSafeCylinder H rho a ha) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice D.time).carrier → Type _) :=
    ⟨(F.metric D.time).toRiemannianMetric⟩
  let : EMetricSpace (F.slice D.time).carrier :=
    .ofRiemannianMetric (𝓡 3) (F.slice D.time).carrier
  have hUopen : IsOpen ((F.metric D.time).ball D.center (rho / 2)) := by
    change IsOpen {z | edist D.center z < ENNReal.ofReal (rho / 2)}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U : TopologicalSpace.Opens (F.slice D.time).carrier :=
    ⟨(F.metric D.time).ball D.center (rho / 2), hUopen⟩
  have hcenter : D.center ∈ U := by
    change edist D.center D.center < ENNReal.ofReal (rho / 2)
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr (half_pos hrho)
  have hUsmall : (U : Set (F.slice D.time).carrier) ⊆
      (F.metric D.time).ball D.center D.radius := by
    intro z hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal ((half_le_self hrho.le).trans hradius))
  have hsmallTime : Icc (-a) 0 ⊆ Icc (-(rho / 2) ^ 2) 0 := by
    intro s hs
    refine ⟨?_, hs.2⟩
    nlinarith only [hs.1, hatime]
  have htimeTest : Icc (-a) 0 ⊆ Icc (-D.radius ^ 2) 0 := by
    intro s hs
    refine ⟨?_, hs.2⟩
    nlinarith [hs.1, sq_nonneg (D.radius - rho)]
  let e := D.cylinder.restrict htimeTest ordConnected_Icc hUsmall
  have htime : ∀ s ∈ Icc (-a) 0,
      D.time + s / 1 ∈ H.spacetime.history.generalized.interval := by
    intro s hs
    rw [H.spacetime.history.interval_eq]
    change D.time + s / 1 ∈ Icc 0 D.time
    exact ⟨F.time_domain_nonnegative (e.time_subset (mem_image_of_mem _ hs)),
      by simpa only [div_one] using add_le_of_nonpos_right hs.2⟩
  have hreg : ∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (D.time + s / 1) := by
    intro s hs
    rintro z ⟨y, hy, rfl⟩
    exact (D.cylinder.regular_image_smaller_closed (half_pos hrho)
      ((half_lt_self hrho).trans_le hradius) (hsmallTime hs)).choose_spec
        ⟨y, hUsmall hy, rfl⟩
  obtain ⟨d, forward, metric⟩ := H.spacetime.history.cylinders_from_surgery
    (F.slice D.time) D.time 1 (Icc (-a) 0) U hUopen htime e hreg
  have hcurv : ∀ s hs z, z ∈ U →
      (F.connection (D.time + s / 1)).curvatureTensorNorm (e.forward s hs z) ≤ rho⁻¹ ^ 2 := by
    intro s hs z hz
    apply (D.curvature s (htimeTest hs) z (hUsmall hz)).trans
    exact pow_le_pow_left₀ (inv_nonneg.mpr D.radius_pos.le)
      ((inv_le_inv₀ D.radius_pos hrho).mpr hradius) 2
  have hbase : ∀ hzero z, z ∈ U → HEq (e.forward 0 hzero z) z :=
    fun hzero z hz => D.based (htimeTest hzero) z (hUsmall hz)
  refine ⟨{
    source := U
    source_eq := rfl
    center_mem := hcenter
    cylinder := d
    time_subset := ?_
    physical_eq := ?_
    based := ?_
    metric_lower := ?_
    scalar_upper := ?_
  }⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  · ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      change D.time + s / 1 ∈ Icc (D.time - a) D.time
      constructor <;> simp only [div_one] <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨t - D.time, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      simp only [parabolicTimeInv, div_one, add_sub_cancel]
  · intro hzero
    rw [(H.spacetime.geometry.sliceIdentification D.time).identification_eq]
    change d.pointMap 0 hzero D.center =
      (⟨D.time, H.center⟩ : H.spacetime.history.generalized.point)
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply test_point_heq H.spacetime.history.history (htime 0 hzero) H.time_mem (by simp)
    exact (heq_of_eq (forward 0 hzero D.center hcenter)).trans
      ((hbase hzero D.center hcenter).trans (heq_of_eq H.center_eq.symm))
  · intro s hs z v
    rw [metric s hs z.val z.property v v]
    have hshort : 6 * rho⁻¹ ^ 2 * (-s) ≤ 1 / 2 := by
      have h := mul_le_mul_of_nonneg_left (show -s ≤ rho ^ 2 / 12 by linarith [hs.1])
        (by positivity : 0 ≤ 6 * rho⁻¹ ^ 2)
      have hcancel : 6 * rho⁻¹ ^ 2 * (rho ^ 2 / 12) = 1 / 2 := by
        field_simp [hrho.ne']
        ring
      rwa [hcancel] at h
    have h := (based_cylinder_metric_comparison_two P44 hpinch e hUopen hbase z.property v
      hs hshort (fun r hr => hcurv r hr z.val z.property)).1
    change (1 / 2 : ℝ) * (F.metric D.time).inner z.val v v ≤
      1 * (F.metric (D.time + s / 1)).inner (e.forward s hs z.val)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) z.val v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) z.val v)
    linarith
  · intro w
    let s := cylinderClockHomeomorph D.time 1 d.scale_pos (safeTestInterval a ha) w.1
    change horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
      (d.pointMap s.val s.property w.2.val) ≤ 9 * rho⁻¹ ^ 2
    rw [historyCylinder_scalar_pullback H.spacetime.history H.spacetime.geometry P.m13
      e d Subset.rfl htime forward s.property w.2.property]
    have h := M44.abs_scalar_le_curvatureTensorNorm
      (F.connection (D.time + s.val / 1)) (e.forward s.val s.property w.2.val)
    norm_num only [Nat.cast_ofNat, Nat.reducePow] at h
    exact (le_abs_self _).trans (h.trans
      (mul_le_mul_of_nonneg_left (hcurv s.val s.property w.2.val w.2.property) (by norm_num)))

end PoincareConjecture.Proofs.M46
