import PoincareConjecture.Proofs.M47.SeedM15CompactPath
import PoincareConjecture.Proofs.M47.SeedM15TestHistory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function

universe u

namespace PoincareConjecture.M47

open Proofs.M12 Proofs.M46

private theorem history_spatial_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {s t : ℝ} (hs : s ∈ G.interval) (ht : t ∈ G.interval)
    {x : (G.slice s).carrier} {y : (G.slice t).carrier} (hst : s = t)
    (h : HEq (H.forward s hs x) (H.forward t ht y)) : HEq x y := by
  subst t
  exact heq_of_eq ((H.forward_openEmbedding s hs).injective (eq_of_heq h))

private theorem history_forward_heq {F : SurgeryFlowData.{u}}
    {G : GeneralizedRicciFlowData.{u}} (H : M33RegularHistoryRealization G F)
    {p q : G.point} (h : p = q) (hp : p.1 ∈ G.interval) (hq : q.1 ∈ G.interval) :
    HEq (H.forward p.1 hp p.2) (H.forward q.1 hq q.2) := by
  cases h
  rfl

theorem seedM15_component_path_capture
    {F : SurgeryFlowData.{u}} {W : M33RegularHistoryWindow F}
    (R : M46RegularSpacetimeData W) {T b S : ℝ}
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hcompact : IsCompact (U : Set (F.slice T).carrier))
    (e : SurgeryFlowCylinder F (F.slice T) T 1 (Icc b 0) U)
    (hinterval : Icc (T + b) T ⊆ R.history.generalized.interval)
    (hbased : ∀ h z, z ∈ U → HEq (e.forward 0 h z) z)
    (hT : T ∈ R.history.generalized.interval)
    (center : (R.history.generalized.slice T).carrier) (x0 : U)
    (hcenter : R.history.history.forward T hT center = x0.val)
    {endpoint : R.geometry.toLGeometry.Point}
    (path : M14BackwardPath R.geometry.toLGeometry T 0 S
      ((R.geometry.sliceIdentification T).identification center).val endpoint)
    {tau : ℝ} (htau : tau ∈ Icc 0 S) (hafter : b < -tau)
    (htime : (path.curve tau).1 ∈ R.history.generalized.interval) :
    ∃ s : ℝ, ∃ hs : s ∈ Icc b 0, ∃ z : U,
      s = -tau ∧ HEq
        (R.history.history.forward (path.curve tau).1 htime (path.curve tau).2)
        (e.forward s hs z.val) := by
  have hb : b < 0 := hafter.trans_le (neg_nonpos.mpr htau.1)
  obtain ⟨c, hbc, hctau⟩ := exists_between hafter
  have hc : c < 0 := hctau.trans_le (neg_nonpos.mpr htau.1)
  let J : SpacetimeInterval := {
    domain := Icc c 0
    ordConnected := ordConnected_Icc
    nontrivial := ⟨c, ⟨le_rfl, hc.le⟩, 0, ⟨hc.le, le_rfl⟩, hc.ne⟩ }
  have hsub : J.domain ⊆ Icc b 0 := Icc_subset_Icc hbc.le le_rfl
  let short := e.restrict hsub J.ordConnected (Subset.refl (U : Set (F.slice T).carrier))
  have hclock : ∀ s ∈ J.domain, T + s / 1 ∈ R.history.generalized.interval := by
    intro s hs
    apply hinterval
    simp only [div_one]
    exact ⟨by linarith [(hsub hs).1], by linarith [hs.2]⟩
  have hregular : ∀ s hs, short.forward s hs '' (U : Set (F.slice T).carrier) ⊆
      m33RegularRegion F (T + s / 1) := by
    intro s hs
    exact e.regular_image_of_earlier (hsub hs)
      ⟨b, ⟨le_rfl, hb.le⟩, hbc.trans_le hs.1⟩
  obtain ⟨d, hd, _⟩ := R.history.cylinders_from_surgery (F.slice T) T 1
    J.domain U U.isOpen hclock short hregular
  have hphysical : (cylinderPhysicalInterval T 1 d.scale_pos J).domain ⊆
      R.history.generalized.interval := by
    rintro _ ⟨s, hs, rfl⟩
    exact hclock s hs
  have hzero : 0 ∈ J.domain := ⟨hc.le, le_rfl⟩
  have hbase : d.pointMap 0 hzero x0.val =
      (⟨T, center⟩ : R.history.generalized.point) := by
    apply Sigma.ext (by simp [GeneralizedFlowCylinder.pointMap])
    exact history_spatial_heq R.history.history (hclock 0 hzero) hT (by simp)
      ((heq_of_eq (hd 0 hzero x0.val x0.property)).trans
        ((hbased (hsub hzero) x0.val x0.property).trans (heq_of_eq hcenter.symm)))
  let gamma : Icc 0 tau → R.geometry.realization.spacetime.Point := fun s => path.curve s.val
  let : PreconnectedSpace (Icc 0 tau) := Subtype.preconnectedSpace isPreconnected_Icc
  have hcont : Continuous gamma := continuousOn_iff_continuous_domRestrict.mp
    (path.curve_continuous.mono (Icc_subset_Icc le_rfl htau.2))
  have htimeGamma : ∀ s, R.geometry.realization.spacetime.timeFunction (gamma s) ∈
      (cylinderPhysicalInterval T 1 d.scale_pos J).domain := by
    intro s
    refine ⟨-s.val, ⟨by linarith [s.property.2], neg_nonpos.mpr s.property.1⟩, ?_⟩
    change T + (-s.val) / 1 = (path.curve s.val).1
    have hpathTime : (path.curve s.val).1 = T - s.val :=
      path.curve_time s.val ⟨s.property.1, s.property.2.trans htau.2⟩
    rw [hpathTime]
    ring
  have hin : ∃ s, gamma s ∈ range (rawCylinderMap R.geometry.realization d) := by
    refine ⟨⟨0, ⟨le_rfl, htau.1⟩⟩,
      ⟨((cylinderClockHomeomorph T 1 d.scale_pos J).symm ⟨0, hzero⟩, x0), ?_⟩⟩
    rw [rawCylinderMap_at_parameter, hbase]
    change (⟨T, center⟩ : R.history.generalized.point) = path.curve 0
    rw [path.curve_start]
    exact ((R.geometry.sliceIdentification T).identification_eq center).symm
  obtain ⟨p, hp⟩ := seedM15_compactCylinder_capture R.geometry.realization d isCompact_Icc
    hcompact hphysical gamma hcont htimeGamma hin ⟨tau, ⟨htau.1, le_rfl⟩⟩
  let q := cylinderClockHomeomorph T 1 d.scale_pos J p.1
  have heq : d.pointMap q.val q.property p.2.val = path.curve tau := hp
  have hparam : q.val = -tau := by
    have h := congrArg Sigma.fst heq
    change T + q.val / 1 = (path.curve tau).1 at h
    have hpathTime : (path.curve tau).1 = T - tau := path.curve_time tau htau
    rw [hpathTime] at h
    linarith
  refine ⟨q.val, hsub q.property, p.2, hparam, ?_⟩
  exact (history_forward_heq R.history.history heq.symm htime (hclock q.val q.property)).trans
    (heq_of_eq (hd q.val q.property p.2.val p.2.property))

end PoincareConjecture.M47
