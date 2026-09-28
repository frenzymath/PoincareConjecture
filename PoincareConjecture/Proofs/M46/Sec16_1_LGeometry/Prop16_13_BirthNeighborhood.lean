import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_RegularBirthLift
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_CylinderRelativeImage
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

open PoincareConjecture.Proofs.M12

private theorem birth_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))





theorem capBirth_positiveTrace_mem_nhdsWithin
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W)
    (R : GeneralizedFlowCarrierConclusion (flowBoxAtlas H.generalized))
    {origin scale d : ℝ} {I : Set ℝ} {J : SpacetimeInterval}
    {U V : TopologicalSpace.Opens (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin scale I U)
    (positive : GeneralizedFlowCylinder H.generalized (F.slice origin)
      origin scale J.domain U)
    (hd : 0 < d) (hVU : (V : Set (F.slice origin).carrier) ⊆ U)
    (hsmall : Icc 0 d ⊆ I) (hpositive : Ioc 0 d ⊆ J.domain)
    (hJI : J.domain ⊆ I)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (htime : ∀ s ∈ Icc 0 d, origin + s / scale ∈ H.generalized.interval)
    (htimePositive : ∀ s ∈ J.domain, origin + s / scale ∈ H.generalized.interval)
    (hforward : ∀ s hs x, x ∈ U →
      H.history.forward (origin + s / scale) (htimePositive s hs)
        (positive.forward s hs x) = e.forward s (hJI hs) x)
    (horigin : origin ∈ H.generalized.interval)
    (y : (H.generalized.slice origin).carrier)
    (hy : H.history.forward origin horigin y ∈ V) :
    {v : R.spacetime.Point | ∃ s, ∃ hs : s ∈ Ioc 0 d,
      ∃ x ∈ V, positive.pointMap s (hpositive hs) x = v} ∈
      𝓝[R.spacetime.timeFunction ⁻¹' Ioc origin (origin + d / scale)]
        (⟨origin, y⟩ : H.generalized.point) := by
  let K : SpacetimeInterval := {
    domain := Icc 0 d
    ordConnected := ordConnected_Icc
    nontrivial := ⟨0, ⟨le_rfl, hd.le⟩, d, ⟨hd.le, le_rfl⟩, hd.ne⟩
  }
  let small := e.restrict hsmall ordConnected_Icc hVU
  have hzero : (0 : ℝ) ∈ K.domain := ⟨le_rfl, hd.le⟩
  obtain ⟨lift, forward, _metric⟩ := exists_capCylinder_regular_birth_lift H V.isOpen
    small hzero (fun _ hs => hs.1) (fun h x hx => hbase (hsmall h) x (hVU hx)) htime
  have hopen : IsOpen (m33RegularRegion F origin) := by
    rw [← H.regular_range origin horigin]
    exact (H.history.forward_openEmbedding origin horigin).isOpen_range
  let Vreg : TopologicalSpace.Opens (F.slice origin).carrier :=
    ⟨V ∩ m33RegularRegion F origin, V.isOpen.inter hopen⟩
  have hxreg : H.history.forward origin horigin y ∈ Vreg := by
    refine ⟨hy, ?_⟩
    rw [← H.regular_range origin horigin]
    exact mem_range_self y
  have hphysical : (cylinderPhysicalInterval origin scale lift.scale_pos K).domain =
      Icc origin (origin + d / scale) := by
    ext t
    constructor
    · rintro ⟨s, hs, rfl⟩
      change origin + s / scale ∈ Icc origin (origin + d / scale)
      exact ⟨by linarith [div_nonneg hs.1 lift.scale_pos.le],
        add_le_add_right ((div_le_div_iff_of_pos_right lift.scale_pos).mpr hs.2) origin⟩
    · intro ht
      refine ⟨scale * (t - origin), ?_, ?_⟩
      · constructor
        · exact mul_nonneg lift.scale_pos.le (sub_nonneg.mpr ht.1)
        · have := (le_div_iff₀ lift.scale_pos).mp (by linarith [ht.2] :
              t - origin ≤ d / scale)
          nlinarith
      · change origin + scale * (t - origin) / scale = t
        field_simp [lift.scale_pos.ne']
        ring
  have htime' : (cylinderPhysicalInterval origin scale lift.scale_pos K).domain ⊆
      H.generalized.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact htime s hs
  let w : (R.timeIntervals.interval
      (cylinderPhysicalInterval origin scale lift.scale_pos K)).Point × Vreg :=
    ((cylinderClockHomeomorph origin scale lift.scale_pos K).symm ⟨0, hzero⟩,
      ⟨H.history.forward origin horigin y, hxreg⟩)
  have hbirth : rawCylinderMap R lift w = (⟨origin, y⟩ : H.generalized.point) := by
    rw [rawCylinderMap_at_parameter]
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    apply birth_point_heq H.history (htime 0 hzero) horigin (by simp)
    exact (heq_of_eq (forward 0 hzero _ hxreg)).trans
      (hbase (hsmall hzero) _ (hVU hy))
  have hnear := rawCylinder_range_mem_nhdsWithin_clock R lift htime' w
  rw [hbirth] at hnear
  have hclockSubset : R.spacetime.timeFunction ⁻¹' Ioc origin (origin + d / scale) ⊆
      R.spacetime.timeFunction ⁻¹'
        (cylinderPhysicalInterval origin scale lift.scale_pos K).domain := by
    rw [hphysical]
    exact preimage_mono Ioc_subset_Icc_self
  have hnear' := (nhdsWithin_mono _ hclockSubset) hnear
  filter_upwards [hnear', self_mem_nhdsWithin] with v hv hclock
  obtain ⟨z, rfl⟩ := hv
  let s := cylinderClockHomeomorph origin scale lift.scale_pos K z.1
  have hs : s.val ∈ Ioc 0 d := by
    refine ⟨?_, s.property.2⟩
    have htimez : origin < z.1.val := by
      simpa only [mem_preimage, rawCylinderMap_time] using hclock.1
    exact mul_pos lift.scale_pos (sub_pos.mpr htimez)
  refine ⟨s.val, hs, z.2.val, z.2.property.1, ?_⟩
  change positive.pointMap s.val (hpositive hs) z.2.val =
    lift.pointMap s.val s.property z.2.val
  apply congrArg (fun z : (H.generalized.slice (origin + s.val / scale)).carrier =>
    (⟨origin + s.val / scale, z⟩ : H.generalized.point))
  apply (H.history.forward_openEmbedding (origin + s.val / scale)
    (htimePositive s.val (hpositive hs))).injective
  rw [hforward s.val (hpositive hs) z.2.val (hVU z.2.property.1),
    forward s.val s.property z.2.val z.2.property]
  rfl

end PoincareConjecture.Proofs.M46
