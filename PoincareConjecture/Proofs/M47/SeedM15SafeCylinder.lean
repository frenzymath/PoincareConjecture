import PoincareConjecture.Proofs.M47.SeedM15TestHistory
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Lemma16_15_InitialScalar

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M47

open Proofs.M46 Proofs.M12

structure SeedM15SafeCylinder {F : SurgeryFlowData.{u}} {T : ℝ}
    {hT : 0 < T} {hTF : T ∈ F.time_domain} {x : (F.slice T).carrier} {r : ℝ}
    (H : SeedM15TestHistory T hT hTF x r) (rho a : ℝ) (ha : 0 < a) where
  source : TopologicalSpace.Opens (F.slice T).carrier
  source_eq : (source : Set (F.slice T).carrier) = (F.metric T).ball x (rho / 2)
  center_mem : x ∈ source
  cylinder : GeneralizedFlowCylinder H.spacetime.history.generalized (F.slice T)
    T 1 (safeTestInterval a ha).domain source
  time_subset : (cylinderPhysicalInterval T 1 cylinder.scale_pos
    (safeTestInterval a ha)).domain ⊆ H.spacetime.history.generalized.interval
  physical_eq : (cylinderPhysicalInterval T 1 cylinder.scale_pos
    (safeTestInterval a ha)).domain = Icc (T - a) T
  based : ∀ hzero, cylinder.pointMap 0 hzero x =
    ((H.spacetime.geometry.sliceIdentification T).identification H.center).val
  metric_lower : ∀ s hs (z : source) (v : TangentSpace (𝓡 3) z.val),
    (1 / 2 : ℝ) * (F.metric T).inner z.val v v ≤ cylinder.pullbackInner s hs z.val v v
  scalar_upper : ∀ w : (H.spacetime.geometry.realization.timeIntervals.interval
      (cylinderPhysicalInterval T 1 cylinder.scale_pos (safeTestInterval a ha))).Point ×
        source,
    horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
      (rawCylinderMap H.spacetime.geometry.realization cylinder w) ≤ 9 * rho⁻¹ ^ 2

private theorem history_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))

theorem seedM15_safeCylinder (P : M46Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T r : ℝ} {hT : 0 < T} {hTF : T ∈ F.time_domain}
    {x : (F.slice T).carrier} (H : SeedM15TestHistory T hT hTF x r)
    (hpinch : SurgeryFlowPinched F) (hr : 0 < r)
    (test : SurgeryFlowCylinder F (F.slice T) T 1
      (Icc (-r ^ 2) 0) ((F.metric T).ball x r))
    (hbased : ∀ h y, y ∈ (F.metric T).ball x r → HEq (test.forward 0 h y) y)
    (hcurv : ∀ s hs y, y ∈ (F.metric T).ball x r →
      (F.connection (T + s / 1)).curvatureTensorNorm (test.forward s hs y) ≤ r⁻¹ ^ 2)
    {rho a : ℝ} (hrho : 0 < rho) (hradius : rho ≤ r) (ha : 0 < a)
    (hatime : a ≤ rho ^ 2 / 4) (hametric : a ≤ rho ^ 2 / 12) :
    Nonempty (SeedM15SafeCylinder H rho a ha) := by
  let P44 : M44CapPersistencePredecessors.{u} :=
    { curvature := P.m04, ordinary_flow := P.m13.ordinary_flow }
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : (F.slice T).carrier → Type _) :=
    ⟨(F.metric T).toRiemannianMetric⟩
  let : EMetricSpace (F.slice T).carrier :=
    .ofRiemannianMetric (𝓡 3) (F.slice T).carrier
  have hUopen : IsOpen ((F.metric T).ball x (rho / 2)) := by
    change IsOpen {z | edist x z < ENNReal.ofReal (rho / 2)}
    exact isOpen_lt (continuous_const.edist continuous_id) continuous_const
  let U : TopologicalSpace.Opens (F.slice T).carrier :=
    ⟨(F.metric T).ball x (rho / 2), hUopen⟩
  have hcenter : x ∈ U := by
    change edist x x < ENNReal.ofReal (rho / 2)
    simpa only [edist_self] using ENNReal.ofReal_pos.mpr (half_pos hrho)
  have hUsmall : (U : Set (F.slice T).carrier) ⊆ (F.metric T).ball x r := by
    intro z hz
    exact hz.trans_le (ENNReal.ofReal_le_ofReal ((half_le_self hrho.le).trans hradius))
  have hsmallTime : Icc (-a) 0 ⊆ Icc (-(rho / 2) ^ 2) 0 := by
    intro s hs
    exact ⟨by nlinarith only [hs.1, hatime], hs.2⟩
  have htimeTest : Icc (-a) 0 ⊆ Icc (-r ^ 2) 0 := by
    intro s hs
    exact ⟨by nlinarith [hs.1, sq_nonneg (r - rho)], hs.2⟩
  let e := test.restrict htimeTest ordConnected_Icc hUsmall
  have htime : ∀ s ∈ Icc (-a) 0,
      T + s / 1 ∈ H.spacetime.history.generalized.interval := by
    intro s hs
    rw [H.spacetime.history.interval_eq]
    change T + s / 1 ∈ Icc 0 T
    exact ⟨F.time_domain_nonnegative (e.time_subset (mem_image_of_mem _ hs)),
      by simpa only [div_one] using add_le_of_nonpos_right hs.2⟩
  have hreg : ∀ s hs, e.forward s hs '' U ⊆ m33RegularRegion F (T + s / 1) := by
    intro s hs
    rintro z ⟨y, hy, rfl⟩
    exact (test.regular_image_smaller_closed (half_pos hrho)
      ((half_lt_self hrho).trans_le hradius) (hsmallTime hs)).choose_spec
      ⟨y, hUsmall hy, rfl⟩
  obtain ⟨d, forward, metric⟩ := H.spacetime.history.cylinders_from_surgery
    (F.slice T) T 1 (Icc (-a) 0) U hUopen htime e hreg
  have hcurvature : ∀ s hs z, z ∈ U →
      (F.connection (T + s / 1)).curvatureTensorNorm (e.forward s hs z) ≤ rho⁻¹ ^ 2 := by
    intro s hs z hz
    apply (hcurv s (htimeTest hs) z (hUsmall hz)).trans
    exact pow_le_pow_left₀ (inv_nonneg.mpr hr.le)
      ((inv_le_inv₀ hr hrho).mpr hradius) 2
  have hbase : ∀ hzero z, z ∈ U → HEq (e.forward 0 hzero z) z :=
    fun hzero z hz => hbased (htimeTest hzero) z (hUsmall hz)
  refine ⟨{
    source := U
    source_eq := rfl
    center_mem := hcenter
    cylinder := d
    time_subset := ?_
    physical_eq := ?_
    based := ?_
    metric_lower := ?_
    scalar_upper := ?_ }⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  · ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      change T + s / 1 ∈ Icc (T - a) T
      constructor <;> simp only [div_one] <;> linarith [hs.1, hs.2]
    · intro ht
      refine ⟨t - T, ⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
      simp only [parabolicTimeInv, div_one, add_sub_cancel]
  · intro hzero
    rw [(H.spacetime.geometry.sliceIdentification T).identification_eq]
    change d.pointMap 0 hzero x = (⟨T, H.center⟩ : H.spacetime.history.generalized.point)
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply history_point_heq H.spacetime.history.history (htime 0 hzero) H.time_mem (by simp)
    exact (heq_of_eq (forward 0 hzero x hcenter)).trans
      ((hbase hzero x hcenter).trans (heq_of_eq H.center_eq.symm))
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
      hs hshort (fun s hs => hcurvature s hs z.val z.property)).1
    change (1 / 2 : ℝ) * (F.metric T).inner z.val v v ≤
      1 * (F.metric (T + s / 1)).inner (e.forward s hs z.val)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) z.val v)
        (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) z.val v)
    linarith
  · intro w
    let s := cylinderClockHomeomorph T 1 d.scale_pos (safeTestInterval a ha) w.1
    change horizontalScalarCurvature H.spacetime.geometry.toLGeometry.leafwise
      (d.pointMap s.val s.property w.2.val) ≤ 9 * rho⁻¹ ^ 2
    rw [historyCylinder_scalar_pullback H.spacetime.history H.spacetime.geometry P.m13
      e d Subset.rfl htime forward s.property w.2.property]
    have h := M44.abs_scalar_le_curvatureTensorNorm
      (F.connection (T + s.val / 1)) (e.forward s.val s.property w.2.val)
    norm_num only [Nat.cast_ofNat, Nat.reducePow] at h
    exact (le_abs_self _).trans (h.trans
      (mul_le_mul_of_nonneg_left (hcurvature s.val s.property w.2.val w.2.property)
        (by norm_num)))

end PoincareConjecture.M47
