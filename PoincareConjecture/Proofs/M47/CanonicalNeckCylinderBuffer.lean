import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderAlternative
import PoincareConjecture.Proofs.M47.CanonicalNeckCylinderForward










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M47



theorem exists_strictLeft_cylinder_buffer_or_cap
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin a l H : ℝ} {U : Set C.carrier}
    (e : SurgeryFlowCylinder F C origin 1 (Ioc a 0) U)
    (ha : a < 0) (hU : IsOpen U) (hne : U.Nonempty)
    (hl : l < origin + a) (hH : origin < H)
    (hJ : Ico l H ⊆ F.time_domain) :
    (∃ d b : ℝ, d < a ∧ 0 < b ∧ l ≤ origin + d ∧ origin + b < H ∧
      ∃ E : SurgeryFlowCylinder F C origin 1 (Icc d b) U,
        ∀ s (hs : s ∈ Ioc a 0) (hs' : s ∈ Icc d b), ∀ x ∈ U,
          E.forward s hs' x = e.forward s hs x) ∨
    (∃ E : SurgeryFlowCylinder F C origin 1 (Icc a 0) U,
      (∀ s (hs : s ∈ Ioc a 0) (hs' : s ∈ Icc a 0), ∀ x ∈ U,
        E.forward s hs' x = e.forward s hs x) ∧
      ∃ hT : origin + a / 1 ∈ F.surgery_times,
        ∀ [Nonempty (F.slice (origin + a / 1)).carrier],
          ∃ i : Fin (F.event (origin + a / 1) hT).cap_count,
            (E.forward a ⟨le_rfl, ha.le⟩ '' U ∩
              ((F.event (origin + a / 1) hT).caps i).carrier).Nonempty) := by
  have hbottom : origin + a ∈ F.time_domain :=
    hJ ⟨hl.le, (show origin + a < origin by linarith only [ha]).trans hH⟩
  obtain ⟨E0, hE0⟩ := exists_strictLeft_cylinder_closed e ha hU hbottom
  have hJ0 : Icc l origin ⊆ F.time_domain :=
    fun _ ht => hJ ⟨ht.1, ht.2.trans_lt hH⟩
  rcases exists_closed_cylinder_backward_extension_or_cap E0 ha hU hne hl hJ0 with
    hextend | hcap
  · obtain ⟨d, hda, hld, E1, hE1⟩ := hextend
    have hlorigin : l < origin := hl.trans (by linarith only [ha])
    have horigin : origin ∈ F.time_domain := hJ ⟨hlorigin.le, hH⟩
    obtain ⟨t, hot, htH, hfree⟩ := M44.exists_surgery_free_right_interval F horigin hH
    let b := t - origin
    have hb : 0 < b := by dsimp only [b]; linarith only [hot]
    have hbH : origin + b < H := by simpa only [b, add_sub_cancel] using htH
    have hright : Icc origin (origin + b / 1) ⊆ F.time_domain := by
      intro s hs
      exact hJ ⟨hlorigin.le.trans hs.1, hs.2.trans_lt (by simpa only [div_one] using hbH)⟩
    have hrightFree : Disjoint F.surgery_times (Ioc origin (origin + b / 1)) := by
      simpa only [div_one, b, add_sub_cancel] using hfree
    obtain ⟨E, hE⟩ := exists_cylinder_forward_along_ordinary_slab E1 hU
      (hda.trans ha).le hb hright hrightFree
    refine Or.inl ⟨d, b, hda, hb, hld, hbH, E, ?_⟩
    intro s hs hs' x hx
    have hs0 : s ∈ Icc a 0 := Ioc_subset_Icc_self hs
    have hs1 : s ∈ Icc d 0 := ⟨hda.le.trans hs0.1, hs0.2⟩
    exact (hE s hs1 hs' x).trans ((hE1 s hs0 hs1 x).trans (hE0 s hs hs0 x hx))
  · exact Or.inr ⟨E0, hE0, hcap⟩

end PoincareConjecture.Proofs.M47
