import PoincareLib.Geometry.RicciFlow.Surgery.Induction.EpochExtension.Extension.ExtensionSlab

/-!
# Actual old-event interiors under a surgery-flow extension

The event's pre-carrier identification is the displayed conjugation through
the same clock slice. Its retained-set image equality also identifies the
interiors, as required by the cylinder clauses at a surgery.
Source: the continuing-region gluing in Morgan--Tian Definition 15.8, p. 362.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.SurgeryFlowExtension

variable {F : SurgeryFlowData.{u}} (E : SurgeryFlowExtension F)
  {T : ℝ} (hT : T ∈ F.surgery_times) (hT' : T ∈ E.extended.surgery_times)
  [Nonempty (F.slice T).carrier] [Nonempty (E.extended.slice T).carrier]

/-- The actual map between old and extended pre-carriers at one common
pre-surgery clock; no independently chosen event identification is used. -/
noncomputable def eventPreEquivalence
    (t : Ico (F.event T hT).tMinus T) (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Ico (E.extended.event T hT').tMinus T) :
    Diffeomorph (𝓡 3) (𝓡 3)
      (F.slice (F.event T hT).tMinus).carrier
      (E.extended.slice (E.extended.event T hT').tMinus).carrier ∞ :=
  (((F.event T hT).pre_identify t).trans (E.identify t.1 ht)).trans
    ((E.extended.event T hT').pre_identify ⟨t.1, ht'⟩).symm

theorem eventPreEquivalence_apply
    (t : Ico (F.event T hT).tMinus T) (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Ico (E.extended.event T hT').tMinus T)
    (x : (F.slice (F.event T hT).tMinus).carrier) :
    E.eventPreEquivalence hT hT' t ht ht' x =
      ((E.extended.event T hT').pre_identify ⟨t.1, ht'⟩).symm
        (E.identify t.1 ht ((F.event T hT).pre_identify t x)) := rfl

theorem eventPreEquivalence_image
    (t : Ico (F.event T hT).tMinus T) (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Ico (E.extended.event T hT').tMinus T) :
    E.eventPreEquivalence hT hT' t ht ht' '' (F.event T hT).retained_pre =
      (E.extended.event T hT').retained_pre :=
  E.old_retained_pre T hT hT' t ht ht'

theorem eventPreEquivalence_interior
    (t : Ico (F.event T hT).tMinus T) (ht : t.1 ∈ F.time_domain)
    (ht' : t.1 ∈ Ico (E.extended.event T hT').tMinus T) :
    E.eventPreEquivalence hT hT' t ht ht' '' interior (F.event T hT).retained_pre =
      interior (E.extended.event T hT').retained_pre := by
  rw [← E.eventPreEquivalence_image hT hT' t ht ht']
  exact (E.eventPreEquivalence hT hT' t ht ht').toHomeomorph.image_interior _

theorem identify_retained_post_interior :
    E.identify T (F.surgery_times_subset hT) '' interior (F.event T hT).retained_post =
      interior (E.extended.event T hT').retained_post := by
  rw [← E.old_retained_post T hT hT']
  exact (E.identify T (F.surgery_times_subset hT)).toHomeomorph.image_interior _

end PoincareMT.SurgeryFlowExtension
