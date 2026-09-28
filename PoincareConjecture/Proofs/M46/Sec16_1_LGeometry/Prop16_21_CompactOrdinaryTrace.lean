import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_13_RegularBirthLift
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_RegularCylinder

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M46

private theorem ordinary_point_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))

theorem exists_compact_ordinary_history_trace
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (H : M33RegularHistoryData W) {a b : ℝ} (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hNo : Disjoint F.surgery_times (Ioc a b))
    (hwindow : Icc a b ⊆ H.generalized.interval)
    {K : Set (F.slice a).carrier} (hK : IsCompact K)
    (hregular : K ⊆ m33RegularRegion F a) :
    ∃ N : Set H.generalized.point, IsCompact N ∧
      ∀ (t : ℝ) (ht : t ∈ Icc a b) (y : (H.generalized.slice t).carrier),
        ((F.regular_slabs a b hab hJ hNo).identify ⟨t, ht⟩).symm
          (H.history.forward t (hwindow ht) y) ∈ K →
        (⟨t, y⟩ : H.generalized.point) ∈ N := by
  let S := F.regular_slabs a b hab hJ hNo
  have htime : ∀ s ∈ Icc 0 (b - a), a + s / 1 ∈ Icc a b := by
    intro s hs
    constructor <;> simp only [div_one] <;> linarith [hs.1, hs.2]
  let e := F.regularCylinder hab hJ hNo zero_lt_one ordConnected_Icc htime univ
  have hzero : (0 : ℝ) ∈ Icc 0 (b - a) := ⟨le_rfl, sub_nonneg.mpr hab.le⟩
  have hbase : ∀ h x, x ∈ (univ : Set (F.slice a).carrier) →
      HEq (e.forward 0 h x) x := by
    intro h x _
    exact F.regularCylinder_initial hab hJ hNo zero_lt_one ordConnected_Icc htime univ h x
  have htime' : ∀ s ∈ Icc 0 (b - a), a + s / 1 ∈ H.generalized.interval :=
    fun s hs => hwindow (htime s hs)
  obtain ⟨lift, forward, _metric⟩ := exists_capCylinder_regular_birth_lift H isOpen_univ e
    hzero (fun _ hs => hs.1) hbase htime'
  let f : Icc 0 (b - a) × K → H.generalized.point :=
    fun z => lift.pointMap z.1.val z.1.property z.2.val
  have hf : Continuous f := by
    exact lift.embedding.continuous.comp
      (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).subtype_mk
        (fun z => ⟨mem_univ z.2.val, hregular z.2.property⟩)))
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  refine ⟨range f, isCompact_range hf, ?_⟩
  intro t ht y hy
  let x := (S.identify ⟨t, ht⟩).symm (H.history.forward t (hwindow ht) y)
  have hx : x ∈ K := hy
  have hxreg : x ∈ univ ∩ m33RegularRegion F a := ⟨mem_univ x, hregular hx⟩
  have hs : t - a ∈ Icc 0 (b - a) := by constructor <;> linarith [ht.1, ht.2]
  refine ⟨(⟨t - a, hs⟩, ⟨x, hx⟩), ?_⟩
  change lift.pointMap (t - a) hs x = (⟨t, y⟩ : H.generalized.point)
  have hclock : a + (t - a) / 1 = t := by simp
  have hid : (⟨a + (t - a) / 1, htime (t - a) hs⟩ : Icc a b) = ⟨t, ht⟩ :=
    Subtype.ext hclock
  have hphysical : (⟨a + (t - a) / 1, e.forward (t - a) hs x⟩ :
      Σ t, (F.slice t).carrier) = ⟨t, H.history.forward t (hwindow ht) y⟩ := by
    have heq := congrArg (fun r : Icc a b =>
      (⟨r.val, (S.identify r) x⟩ : Σ t, (F.slice t).carrier)) hid
    exact heq.trans (congrArg (Sigma.mk t)
      ((S.identify ⟨t, ht⟩).apply_symm_apply (H.history.forward t (hwindow ht) y)))
  apply Sigma.ext hclock
  apply ordinary_point_heq H.history (htime' (t - a) hs) (hwindow ht) hclock
  exact (heq_of_eq (forward (t - a) hs x hxreg)).trans (Sigma.mk.inj_iff.mp hphysical).2

end PoincareConjecture.Proofs.M46
