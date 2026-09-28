import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_TrackedBall
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction










set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture

namespace SurgeryFlowData

variable (F : SurgeryFlowData.{u}) {a b q : ℝ} (hab : a < b)
  (hJ : Icc a b ⊆ F.time_domain) (hS : Disjoint F.surgery_times (Ioc a b))
  (hq : 0 < q) {I : Set ℝ} (hI : I.OrdConnected)
  (htime : ∀ s ∈ I, a + s / q ∈ Icc a b) (U : Set (F.slice a).carrier)




noncomputable def regularCylinder : SurgeryFlowCylinder F (F.slice a) a q I U := by
  let S := F.regular_slabs a b hab hJ hS
  have event_at_birth (s : ℝ) (hs : s ∈ I) (hT : a + s / q ∈ F.surgery_times) :
      a + s / q = a := by
    apply le_antisymm _ (htime s hs).1
    by_contra h
    exact Set.disjoint_left.mp hS hT ⟨lt_of_not_ge h, (htime s hs).2⟩
  refine {
    scale_pos := hq
    interval_connected := hI
    time_subset := ?_
    forward := fun s hs => S.identify ⟨a + s / q, htime s hs⟩
    inverse := fun s hs => (S.identify ⟨a + s / q, htime s hs⟩).symm
    forward_smooth := fun s hs =>
      (S.identify ⟨a + s / q, htime s hs⟩).contMDiff.contMDiffOn
    inverse_smooth := fun s hs =>
      (S.identify ⟨a + s / q, htime s hs⟩).symm.contMDiff.contMDiffOn
    left_inverse := fun s hs x _ =>
      (S.identify ⟨a + s / q, htime s hs⟩).symm_apply_apply x
    right_inverse := fun s hs x _ =>
      (S.identify ⟨a + s / q, htime s hs⟩).apply_symm_apply x
    slab_compatibility := ?_
    retained_at_surgery := ?_
    pre_retained_at_surgery := ?_
    surgery_compatibility := ?_
  }
  · rintro _ ⟨s, hs, rfl⟩
    exact hJ (htime s hs)
  · intro c d hcd hK hNo s hs t ht hs' ht' x _
    rw [F.slab_transport_coherent c d a b hcd hK hNo hab hJ hS
      (a + s / q) (a + t / q) hs' ht' (htime s hs) (htime t ht)]
    exact congrArg (S.identify ⟨a + t / q, htime t ht⟩)
      ((S.identify ⟨a + s / q, htime s hs⟩).symm_apply_apply x)
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



theorem regularCylinder_initial (hzero : (0 : ℝ) ∈ I) (x : (F.slice a).carrier) :
    HEq ((F.regularCylinder hab hJ hS hq hI htime U).forward 0 hzero x) x := by
  exact (F.regular_slabs a b hab hJ hS).identify_initial_heq
    ⟨a + 0 / q, htime 0 hzero⟩ (by simp) x



theorem regularCylinder_pullbackInner (s : ℝ) (hs : s ∈ I)
    (x : (F.slice a).carrier) (v w : TangentSpace (𝓡 3) x) :
    (F.regularCylinder hab hJ hS hq hI htime U).pullbackInner s hs x v w =
      q * ((F.regular_slabs a b hab hJ hS).flow.metric (a + s / q)).inner x v w := by
  exact congrArg (fun z : ℝ => q * z)
    ((F.regular_slabs a b hab hJ hS).metric_pullback
      ⟨a + s / q, htime s hs⟩ x v w)

end SurgeryFlowData

end PoincareConjecture
