import PoincareConjecture.Proofs.M56.PointGroups
import PoincareConjecture.Proofs.M33.RegularHistory
import PoincareConjecture.Proofs.M46.Sec16_3_Assembly.FiniteEventInduction

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture

theorem m56PointGroups_induction (F : SurgeryFlowData.{u})
    (hzero : M56PointGroups (F.slice 0))
    (hevent : ∀ (s : ℝ) (hs : s ∈ F.surgery_times)
      (hpost : Nonempty (F.slice s).carrier), letI := hpost
      M56PointGroups (F.slice (F.event s hs).tMinus) → M56PointGroups (F.slice s))
    (T : ℝ) (hT : T ∈ F.time_domain) : M56PointGroups (F.slice T) := by
  have hJ : Icc 0 T ⊆ F.time_domain := F.time_domain_interval.out F.zero_mem hT
  have hfinite : (F.surgery_times ∩ Ioc 0 T).Finite :=
    (F.surgery_times_finite_on_compact isCompact_Icc hJ).subset
      (inter_subset_inter_right _ Ioc_subset_Icc_self)
  apply Proofs.M46.finite_event_forward_induction (F.time_domain_nonnegative hT)
    hfinite (fun t => M56PointGroups (F.slice t)) hzero
  · intro a ha b hb hab hfree hA
    rcases hab.eq_or_lt with rfl | hab
    · exact hA
    · let B := F.regular_slabs a b hab
        (fun t ht => hJ ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩) hfree
      exact m56PointGroups_transport (B.identify ⟨b, hab.le, le_rfl⟩) hA
  · intro s hs ih x
    let hpost : Nonempty (F.slice s).carrier := ⟨x⟩
    let := hpost
    exact hevent s hs.1 hpost
      (ih (F.event s hs.1).tMinus
        ⟨(F.event s hs.1).tMinus_nonnegative, (F.event s hs.1).tMinus_lt⟩) x

theorem m56PointGroups_of_witness (F : SurgeryFlowData.{u})
    (W : RepairedEventChildWitness F) (hzero : M56PointGroups (F.slice 0))
    (T : ℝ) (hT : T ∈ F.time_domain) : M56PointGroups (F.slice T) := by
  apply m56PointGroups_induction F hzero _ T hT
  intro s hs hpost _
  exact m56PointGroups_of_survivors (W.topology s hs hpost)
    (W.children s hs hpost).survivor_group_subsingleton

end PoincareConjecture
