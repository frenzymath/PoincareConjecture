import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_RegularCylinder










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture



theorem SurgeryRegularSlab.transport_initial
    {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {a b : ℝ}
    (S : SurgeryRegularSlab slice metric a b) (t : Icc a b)
    (x : (slice a).carrier) :
    S.transport ⟨a, ⟨le_rfl, S.ordered.le⟩⟩ t x = S.identify t x := by
  have hi : (S.identify ⟨a, ⟨le_rfl, S.ordered.le⟩⟩).symm x = x := by
    exact (S.initial_identify ((S.identify ⟨a, ⟨le_rfl, S.ordered.le⟩⟩).symm x)).symm.trans
      ((S.identify ⟨a, ⟨le_rfl, S.ordered.le⟩⟩).apply_symm_apply x)
  simp only [SurgeryRegularSlab.transport, hi]

namespace SurgeryFlowData



theorem regular_identify_coherent (F : SurgeryFlowData.{u}) {a b c t : ℝ}
    (hab : a < b) (hJ : Icc a b ⊆ F.time_domain)
    (hS : Disjoint F.surgery_times (Ioc a b))
    (hac : a < c) (hK : Icc a c ⊆ F.time_domain)
    (hT : Disjoint F.surgery_times (Ioc a c))
    (ht : t ∈ Icc a b) (ht' : t ∈ Icc a c) (x : (F.slice a).carrier) :
    (F.regular_slabs a b hab hJ hS).identify ⟨t, ht⟩ x =
      (F.regular_slabs a c hac hK hT).identify ⟨t, ht'⟩ x := by
  have h := F.slab_transport_coherent a b a c hab hJ hS hac hK hT a t
    ⟨le_rfl, hab.le⟩ ht ⟨le_rfl, hac.le⟩ ht' x
  simpa only [SurgeryRegularSlab.transport_initial] using h

variable (F : SurgeryFlowData.{u}) {a b : ℝ}
  (hJ : Ico a b ⊆ F.time_domain) (hS : Disjoint F.surgery_times (Ioo a b))



noncomputable def regularIdentifyIco (t : Ico a b) :
    Diffeomorph (𝓡 3) (𝓡 3) (F.slice a).carrier (F.slice t.1).carrier ∞ := by
  have hac : a < (t.1 + b) / 2 := by linarith [t.2.1, t.2.2]
  have hcb : (t.1 + b) / 2 < b := by linarith [t.2.2]
  have hK : Icc a ((t.1 + b) / 2) ⊆ F.time_domain :=
    fun _ hs => hJ ⟨hs.1, hs.2.trans_lt hcb⟩
  have hT : Disjoint F.surgery_times (Ioc a ((t.1 + b) / 2)) :=
    Set.disjoint_left.mpr fun _ hs ht =>
      Set.disjoint_left.mp hS hs ⟨ht.1, ht.2.trans_lt hcb⟩
  exact (F.regular_slabs a ((t.1 + b) / 2) hac hK hT).identify
    ⟨t.1, t.2.1, by linarith [t.2.2]⟩



theorem regularIdentifyIco_eq (t : Ico a b) {c : ℝ}
    (hac : a < c) (hK : Icc a c ⊆ F.time_domain)
    (hT : Disjoint F.surgery_times (Ioc a c)) (ht : t.1 ∈ Icc a c)
    (x : (F.slice a).carrier) :
    F.regularIdentifyIco hJ hS t x =
      (F.regular_slabs a c hac hK hT).identify ⟨t.1, ht⟩ x := by
  unfold regularIdentifyIco
  exact F.regular_identify_coherent _ _ _ hac hK hT _ ht x



theorem regularIdentifyIco_transport {c d : ℝ} (hcd : c < d)
    (hK : Icc c d ⊆ F.time_domain) (hT : Disjoint F.surgery_times (Ioc c d))
    (s t : Ico a b) (hs : s.1 ∈ Icc c d) (ht : t.1 ∈ Icc c d)
    (x : (F.slice a).carrier) :
    (F.regular_slabs c d hcd hK hT).transport ⟨s.1, hs⟩ ⟨t.1, ht⟩
      (F.regularIdentifyIco hJ hS s x) = F.regularIdentifyIco hJ hS t x := by
  let z := (max s.1 t.1 + b) / 2
  have hmax : max s.1 t.1 < b := max_lt s.2.2 t.2.2
  have hsz : s.1 ≤ z := by dsimp [z]; linarith [le_max_left s.1 t.1]
  have htz : t.1 ≤ z := by dsimp [z]; linarith [le_max_right s.1 t.1]
  have haz : a < z := by dsimp [z]; linarith [s.2.1, le_max_left s.1 t.1]
  have hzb : z < b := by dsimp [z]; linarith
  have hL : Icc a z ⊆ F.time_domain := fun _ hu => hJ ⟨hu.1, hu.2.trans_lt hzb⟩
  have hV : Disjoint F.surgery_times (Ioc a z) :=
    Set.disjoint_left.mpr fun _ hs ht =>
      Set.disjoint_left.mp hS hs ⟨ht.1, ht.2.trans_lt hzb⟩
  rw [F.regularIdentifyIco_eq hJ hS s haz hL hV ⟨s.2.1, hsz⟩,
    F.regularIdentifyIco_eq hJ hS t haz hL hV ⟨t.2.1, htz⟩]
  rw [F.slab_transport_coherent c d a z hcd hK hT haz hL hV
    s.1 t.1 hs ht ⟨s.2.1, hsz⟩ ⟨t.2.1, htz⟩]
  exact congrArg ((F.regular_slabs a z haz hL hV).identify ⟨t.1, t.2.1, htz⟩)
    (((F.regular_slabs a z haz hL hV).identify ⟨s.1, s.2.1, hsz⟩).symm_apply_apply x)

variable {q : ℝ} (hq : 0 < q) {I : Set ℝ} (hI : I.OrdConnected)
  (htime : ∀ s ∈ I, a + s / q ∈ Ico a b) (U : Set (F.slice a).carrier)



noncomputable def regularCylinderIco : SurgeryFlowCylinder F (F.slice a) a q I U := by
  have event_at_birth (s : ℝ) (hs : s ∈ I) (hT : a + s / q ∈ F.surgery_times) :
      a + s / q = a := by
    apply le_antisymm _ (htime s hs).1
    by_contra h
    exact Set.disjoint_left.mp hS hT ⟨lt_of_not_ge h, (htime s hs).2⟩
  refine {
    scale_pos := hq
    interval_connected := hI
    time_subset := ?_
    forward := fun s hs => F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩
    inverse := fun s hs => (F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩).symm
    forward_smooth := fun s hs =>
      (F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩).contMDiff.contMDiffOn
    inverse_smooth := fun s hs =>
      (F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩).symm.contMDiff.contMDiffOn
    left_inverse := fun s hs x _ =>
      (F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩).symm_apply_apply x
    right_inverse := fun s hs x _ =>
      (F.regularIdentifyIco hJ hS ⟨a + s / q, htime s hs⟩).apply_symm_apply x
    slab_compatibility := ?_
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_
  }
  · rintro _ ⟨s, hs, rfl⟩
    exact hJ (htime s hs)
  · intro c d hcd hK hT s hs t ht hs' ht' x _
    exact F.regularIdentifyIco_transport hJ hS hcd hK hT
      ⟨a + s / q, htime s hs⟩ ⟨a + t / q, htime t ht⟩ hs' ht' x
  · intro s hs hT _ hearlier
    obtain ⟨s', hs', hlt⟩ := hearlier
    have hclock : a + s' / q < a + s / q := by
      linarith [(div_lt_div_iff_of_pos_right hq).mpr hlt]
    rw [event_at_birth s hs hT] at hclock
    exact ((not_lt_of_ge (htime s' hs').1) hclock).elim
  · intro s hs hT _ t ht ht' x _
    have hbefore := ht'.2
    rw [event_at_birth s hs hT] at hbefore
    exact ((not_lt_of_ge (htime t ht).1) hbefore).elim
  · intro s hs hT _ t ht ht' x _
    have hbefore := ht'.2
    rw [event_at_birth s hs hT] at hbefore
    exact ((not_lt_of_ge (htime t ht).1) hbefore).elim



theorem regularCylinderIco_initial (hzero : (0 : ℝ) ∈ I) (x : (F.slice a).carrier) :
    HEq ((F.regularCylinderIco hJ hS hq hI htime U).forward 0 hzero x) x := by
  change HEq (F.regularIdentifyIco hJ hS ⟨a + 0 / q, htime 0 hzero⟩ x) x
  unfold regularIdentifyIco
  exact SurgeryRegularSlab.identify_initial_heq _ _ (by simp) x

end SurgeryFlowData

end PoincareConjecture
