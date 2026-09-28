import PoincareConjecture.Proofs.M56.ComponentTrace
import PoincareConjecture.Proofs.M56.EventOverlap

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

noncomputable def m56Trace_eventExtension {F : SurgeryFlowData.{u}} {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (P : M56ComponentTrace F (F.event T hT).tMinus)
    (z : (F.slice (F.event T hT).tMinus).carrier)
    (hz : z ∈ connectedComponent (P.point
      ⟨(F.event T hT).tMinus, (F.event T hT).tMinus_nonnegative, le_rfl⟩))
    (y : (F.slice T).carrier) (hret : z ∈ interior (F.event T hT).retained_pre)
    (hchild : (F.event T hT).retention.map z ∈ connectedComponent y) :
    M56ComponentTrace F T := by
  classical
  let E := F.event T hT
  let p : ∀ s : Icc (0 : ℝ) T, (F.slice s.1).carrier := fun s =>
    if hsT : s.1 = T then hsT.symm ▸ y
    else if hsa : s.1 ≤ E.tMinus then P.point ⟨s.1, s.2.1, hsa⟩
    else E.pre_identify ⟨s.1, (lt_of_not_ge hsa).le, lt_of_le_of_ne s.2.2 hsT⟩ z
  have old (s : Icc (0 : ℝ) T) (hsa : s.1 ≤ E.tMinus) :
      p s = P.point ⟨s.1, s.2.1, hsa⟩ := by
    simp only [p, dif_neg (ne_of_lt (hsa.trans_lt E.tMinus_lt)), dif_pos hsa]
  have pre (s : Icc (0 : ℝ) T) (hsT : s.1 ≠ T) (hsa : ¬ s.1 ≤ E.tMinus) :
      p s = E.pre_identify
        ⟨s.1, (lt_of_not_ge hsa).le, lt_of_le_of_ne s.2.2 hsT⟩ z := by
    simp only [p, dif_neg hsT, dif_neg hsa]
  have terminal : p ⟨T, E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩ = y := by
    simp only [p, ↓reduceDIte]
  refine {
    time_subset := F.time_domain_interval.out F.zero_mem (F.surgery_times_subset hT)
    point := p
    regular := ?_
    inherited := ?_ }
  · intro c d hcd hK hfree s t hs ht
    let B := F.regular_slabs c d hcd hK hfree
    by_cases hsT : s.1 = T
    · have htT : t.1 = T := by
        by_contra htT
        exact Set.disjoint_left.mp hfree hT
          ⟨ht.1.trans_lt (lt_of_le_of_ne t.2.2 htT), hsT ▸ hs.2⟩
      have hst : s = t := Subtype.ext (hsT.trans htT.symm)
      subst t
      rfl
    by_cases htT : t.1 = T
    · exact False.elim (Set.disjoint_left.mp hfree hT
        ⟨hs.1.trans_lt (lt_of_le_of_ne s.2.2 hsT), htT ▸ ht.2⟩)
    have cross (s t : Icc (0 : ℝ) T) (hs : s.1 ∈ Icc c d) (ht : t.1 ∈ Icc c d)
        (htT : t.1 ≠ T) (hsa : s.1 ≤ E.tMinus) (hta : ¬ t.1 ≤ E.tMinus) :
        ConnectedComponents.mk ((B.identify ⟨s.1, hs⟩).symm (p s)) =
          ConnectedComponents.mk ((B.identify ⟨t.1, ht⟩).symm (p t)) := by
      have hacd : E.tMinus ∈ Icc c d :=
        ⟨hs.1.trans hsa, (lt_of_not_ge hta).le.trans ht.2⟩
      have hP := P.regular c d hcd hK hfree
        ⟨s.1, s.2.1, hsa⟩ ⟨E.tMinus, E.tMinus_nonnegative, le_rfl⟩ hs hacd
      have hZ := m56ComponentClass_map (B.identify ⟨E.tMinus, hacd⟩).symm.continuous
        (ConnectedComponents.coe_eq_coe'.mpr hz)
      have hE := m56Event_pullback_eq F hT hcd hK hfree E.tMinus t.1 hacd ht
        ⟨le_rfl, E.tMinus_lt⟩ ⟨(lt_of_not_ge hta).le, lt_of_le_of_ne t.2.2 htT⟩ z
      change (B.identify ⟨E.tMinus, hacd⟩).symm
          (E.pre_identify ⟨E.tMinus, le_rfl, E.tMinus_lt⟩ z) =
        (B.identify ⟨t.1, ht⟩).symm
          (E.pre_identify ⟨t.1, (lt_of_not_ge hta).le, lt_of_le_of_ne t.2.2 htT⟩ z) at hE
      rw [E.pre_initial z] at hE
      rw [old s hsa, pre t htT hta]
      exact hP.trans (hZ.symm.trans (congrArg ConnectedComponents.mk hE))
    by_cases hsa : s.1 ≤ E.tMinus
    · by_cases hta : t.1 ≤ E.tMinus
      · rw [old s hsa, old t hta]
        exact P.regular c d hcd hK hfree
          ⟨s.1, s.2.1, hsa⟩ ⟨t.1, t.2.1, hta⟩ hs ht
      · exact cross s t hs ht htT hsa hta
    · by_cases hta : t.1 ≤ E.tMinus
      · exact (cross t s ht hs hsT hta hsa).symm
      · rw [pre s hsT hsa, pre t htT hta]
        exact congrArg ConnectedComponents.mk
          (m56Event_pullback_eq F hT hcd hK hfree s.1 t.1 hs ht
            ⟨(lt_of_not_ge hsa).le, lt_of_le_of_ne s.2.2 hsT⟩
            ⟨(lt_of_not_ge hta).le, lt_of_le_of_ne t.2.2 htT⟩ z)
  · intro s hs hpost
    let := hpost
    by_cases hsT : s.1 = T
    · have hsEq : s = ⟨T, E.tMinus_nonnegative.trans E.tMinus_lt.le, le_rfl⟩ :=
        Subtype.ext hsT
      subst s
      refine ⟨z, ?_, hret, ?_⟩
      · rwa [old _ le_rfl]
      · rwa [terminal]
    · have hsa : s.1 ≤ E.tMinus := by
        by_contra hsa
        exact Set.disjoint_left.mp (m56Event_gap F hT) hs
          ⟨lt_of_not_ge hsa, lt_of_le_of_ne s.2.2 hsT⟩
      have hpre : (F.event s.1 hs).tMinus ≤ E.tMinus :=
        (F.event s.1 hs).tMinus_lt.le.trans hsa
      obtain ⟨x, hx, hxi, hxr⟩ := P.inherited ⟨s.1, s.2.1, hsa⟩ hs hpost
      refine ⟨x, ?_, hxi, ?_⟩
      · rwa [old _ hpre]
      · rwa [old _ hsa]

theorem m56Trace_eventExtension_terminal {F : SurgeryFlowData.{u}} {T : ℝ}
    (hT : T ∈ F.surgery_times) [Nonempty (F.slice T).carrier]
    (P : M56ComponentTrace F (F.event T hT).tMinus)
    (z : (F.slice (F.event T hT).tMinus).carrier)
    (hz : z ∈ connectedComponent (P.point
      ⟨(F.event T hT).tMinus, (F.event T hT).tMinus_nonnegative, le_rfl⟩))
    (y : (F.slice T).carrier) (hret : z ∈ interior (F.event T hT).retained_pre)
    (hchild : (F.event T hT).retention.map z ∈ connectedComponent y) :
    (m56Trace_eventExtension hT P z hz y hret hchild).point
      ⟨T, F.time_domain_nonnegative (F.surgery_times_subset hT), le_rfl⟩ = y := by
  simp only [m56Trace_eventExtension, ↓reduceDIte]

end PoincareConjecture
