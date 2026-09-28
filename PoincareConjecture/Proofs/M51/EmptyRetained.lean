import PoincareConjecture.Proofs.M51.EmptyEvents

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M51Empty

variable (F : SurgeryFlowData.{u}) {a : ℝ} (ha : a ∈ F.time_domain)
    [IsEmpty (F.slice a).carrier] (T : ℝ) (hT : T ∈ F.surgery_times)
    [Nonempty (F.slice T).carrier] [Nonempty (slice F a T).carrier]

theorem event_reference_inverse (t : Ico (F.event T hT).tMinus T)
    (ht : t.1 ∈ F.time_domain) (x : (F.slice (F.event T hT).tMinus).carrier) :
    ((event F ha T hT).pre_identify t).symm
      (identify F ha t.1 ht ((F.event T hT).pre_identify t x)) =
        M51EventCopy.identify F.slice (fun s => min s a) (F.event T hT).tMinus
          (event_clock F ha T hT _ (F.event T hT).tMinus_lt.le) x := by
  rw [identify_of_le F ha t.1 ht (t.2.2.le.trans (F.surgeryTime_le_empty ha hT))]
  change (((F.event T hT).reindexPast (fun s => min s a)
    (event_clock F ha T hT)).pre_identify t).symm _ = _
  have h := (F.event T hT).reindexPast_pre_identify_apply
    (fun s => min s a) (event_clock F ha T hT) t x
  exact (congrArg (((F.event T hT).reindexPast (fun s => min s a)
    (event_clock F ha T hT)).pre_identify t).symm h.symm).trans
      (Diffeomorph.symm_apply_apply _ _)

theorem event_retained_post :
    identify F ha T (F.surgery_times_subset hT) '' (F.event T hT).retained_post =
      (event F ha T hT).retained_post := by
  rw [identify_of_le F ha T (F.surgery_times_subset hT) (F.surgeryTime_le_empty ha hT)]
  exact (F.event T hT).reindexPast_retained_post_image
    (fun s => min s a) (event_clock F ha T hT)

theorem event_retained_pre (t : Ico (F.event T hT).tMinus T)
    (ht : t.1 ∈ F.time_domain) :
    (fun x => ((event F ha T hT).pre_identify t).symm
      (identify F ha t.1 ht ((F.event T hT).pre_identify t x))) ''
        (F.event T hT).retained_pre = (event F ha T hT).retained_pre := by
  have heq : (fun x => ((event F ha T hT).pre_identify t).symm
      (identify F ha t.1 ht ((F.event T hT).pre_identify t x))) =
        M51EventCopy.identify F.slice (fun s => min s a) (F.event T hT).tMinus
          (event_clock F ha T hT _ (F.event T hT).tMinus_lt.le) :=
    funext (event_reference_inverse F ha T hT t ht)
  rw [heq]
  exact (F.event T hT).reindexPast_retained_pre_image
    (fun s => min s a) (event_clock F ha T hT)

theorem event_retention (t : Ico (F.event T hT).tMinus T)
    (ht : t.1 ∈ F.time_domain) (x : (F.slice (F.event T hT).tMinus).carrier) :
    identify F ha T (F.surgery_times_subset hT) ((F.event T hT).retention.map x) =
      (event F ha T hT).retention.map
        (((event F ha T hT).pre_identify t).symm
          (identify F ha t.1 ht ((F.event T hT).pre_identify t x))) := by
  rw [event_reference_inverse F ha T hT t ht x,
    identify_of_le F ha T (F.surgery_times_subset hT) (F.surgeryTime_le_empty ha hT)]
  exact ((F.event T hT).reindexPast_retention_map
    (fun s => min s a) (event_clock F ha T hT) x).symm

end PoincareConjecture.M51Empty
