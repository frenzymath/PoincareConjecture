import PoincareConjecture.Proofs.M56.ComponentTrace









set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture



noncomputable def m56Trace_regularExtension {F : SurgeryFlowData.{u}} {a b : ℝ}
    (P : M56ComponentTrace F a) (ha0 : 0 ≤ a) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (y : (F.slice a).carrier)
    (hy : y ∈ connectedComponent (P.point ⟨a, ha0, le_rfl⟩)) :
    M56ComponentTrace F b := by
  classical
  let S := F.regular_slabs a b hab hJ hfree
  let p : ∀ s : Icc (0 : ℝ) b, (F.slice s.1).carrier := fun s =>
    if hs : s.1 ≤ a then P.point ⟨s.1, s.2.1, hs⟩
    else S.identify ⟨s.1, (lt_of_not_ge hs).le, s.2.2⟩ y
  refine {
    time_subset := ?_
    point := p
    regular := ?_
    inherited := ?_ }
  · intro t ht
    by_cases hta : t ≤ a
    · exact P.time_subset ⟨ht.1, hta⟩
    · exact hJ ⟨(lt_of_not_ge hta).le, ht.2⟩
  · intro c d hcd hK hfree' s t hs ht
    let B := F.regular_slabs c d hcd hK hfree'
    have cross (s t : Icc (0 : ℝ) b) (hs : s.1 ∈ Icc c d) (ht : t.1 ∈ Icc c d)
        (hsa : s.1 ≤ a) (hta : ¬ t.1 ≤ a) :
        ConnectedComponents.mk ((B.identify ⟨s.1, hs⟩).symm (p s)) =
          ConnectedComponents.mk ((B.identify ⟨t.1, ht⟩).symm (p t)) := by
      have hacd : a ∈ Icc c d := ⟨hs.1.trans hsa, (lt_of_not_ge hta).le.trans ht.2⟩
      have hP := P.regular c d hcd hK hfree'
        ⟨s.1, s.2.1, hsa⟩ ⟨a, ha0, le_rfl⟩ hs hacd
      have hY := m56ComponentClass_map (B.identify ⟨a, hacd⟩).symm.continuous
        (ConnectedComponents.coe_eq_coe'.mpr hy)
      have hS := m56Slab_pullback_eq F hcd hK hfree' hab hJ hfree a t.1
        hacd ht ⟨le_rfl, hab.le⟩ ⟨(lt_of_not_ge hta).le, t.2.2⟩ y
      change (B.identify ⟨a, hacd⟩).symm (S.identify ⟨a, le_rfl, hab.le⟩ y) =
        (B.identify ⟨t.1, ht⟩).symm
          (S.identify ⟨t.1, (lt_of_not_ge hta).le, t.2.2⟩ y) at hS
      rw [S.initial_identify y] at hS
      simpa only [p, dif_pos hsa, dif_neg hta] using
        hP.trans (hY.symm.trans (congrArg ConnectedComponents.mk hS))
    by_cases hsa : s.1 ≤ a
    · by_cases hta : t.1 ≤ a
      · simpa only [p, dif_pos hsa, dif_pos hta] using
          P.regular c d hcd hK hfree' ⟨s.1, s.2.1, hsa⟩ ⟨t.1, t.2.1, hta⟩ hs ht
      · exact cross s t hs ht hsa hta
    · by_cases hta : t.1 ≤ a
      · exact (cross t s ht hs hta hsa).symm
      · simpa only [p, dif_neg hsa, dif_neg hta] using congrArg ConnectedComponents.mk
          (m56Slab_pullback_eq F hcd hK hfree' hab hJ hfree s.1 t.1 hs ht
            ⟨(lt_of_not_ge hsa).le, s.2.2⟩ ⟨(lt_of_not_ge hta).le, t.2.2⟩ y)
  · intro s hs hpost
    let := hpost
    have hsa : s.1 ≤ a := by
      by_contra h
      exact Set.disjoint_left.mp hfree hs ⟨lt_of_not_ge h, s.2.2⟩
    have hpre : (F.event s.1 hs).tMinus ≤ a := (F.event s.1 hs).tMinus_lt.le.trans hsa
    simpa only [p, dif_pos hsa, dif_pos hpre] using
      P.inherited ⟨s.1, s.2.1, hsa⟩ hs hpost



theorem m56Trace_regularExtension_terminal {F : SurgeryFlowData.{u}} {a b : ℝ}
    (P : M56ComponentTrace F a) (ha0 : 0 ≤ a) (hab : a < b)
    (hJ : Icc a b ⊆ F.time_domain) (hfree : Disjoint F.surgery_times (Ioc a b))
    (y : (F.slice a).carrier)
    (hy : y ∈ connectedComponent (P.point ⟨a, ha0, le_rfl⟩)) :
    (m56Trace_regularExtension P ha0 hab hJ hfree y hy).point
        ⟨b, ha0.trans hab.le, le_rfl⟩ =
      (F.regular_slabs a b hab hJ hfree).identify ⟨b, hab.le, le_rfl⟩ y := by
  simp only [m56Trace_regularExtension, not_le.mpr hab, ↓reduceDIte]

end PoincareConjecture
