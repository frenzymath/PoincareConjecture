import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderUniqueness












set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44

variable {F : SurgeryFlowData.{u}} {origin scale c d B : ℝ}
  {U V : Set (F.slice origin).carrier}





theorem not_disappears_of_surviving_subcylinder
    (outer : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (inner : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) V)
    (hc : 0 < c) (hcd : c < d) (hVU : V ⊆ U) (hV : V.Nonempty)
    (hinitial : ∀ h x, x ∈ V → HEq (inner.forward 0 h x) x) :
    ¬ SurgeryBallDisappearsAt F outer (origin + c / scale) := by
  obtain ⟨x, hx⟩ := hV
  rintro (hempty | ⟨hT, hn, houter, s0, hs0, hlost⟩)
  · exact hempty.false (inner.forward c ⟨hc.le, hcd⟩ x)
  · let := hn
    obtain ⟨r, hr, hr'⟩ := exists_preterminal_parameter outer.scale_pos hc
      (F.event (origin + c / scale) hT).tMinus_lt
    let s := max s0 r
    have hs : s ∈ Ico (0 : ℝ) c :=
      ⟨le_max_of_le_left hs0.1, max_lt hs0.2 hr.2⟩
    have hsin : s ∈ Ico (0 : ℝ) d := ⟨hs.1, hs.2.trans hcd⟩
    have ht : origin + s / scale ∈
        Ico (F.event (origin + c / scale) hT).tMinus (origin + c / scale) := by
      constructor
      · have hrs : r / scale ≤ s / scale :=
          (div_le_div_iff_of_pos_right outer.scale_pos).mpr (le_max_right s0 r)
        linarith only [hr'.1, hrs]
      · have hsc := (div_lt_div_iff_of_pos_right outer.scale_pos).mpr hs.2
        linarith only [hsc]
    have heq : outer.forward s hs x = inner.forward s hsin x := by
      apply cylinder_forward_eq_of_initial outer inner hs.1
        (fun _ hb => ⟨hb.1, hb.2.trans_lt hs.2⟩)
        (fun _ hb => ⟨hb.1, hb.2.trans_lt hsin.2⟩) x (hVU hx) hx
      exact eq_of_heq ((houter _ x (hVU hx)).trans (hinitial _ x hx).symm)
    have hout := hlost s hs (le_max_left s0 r) x (hVU hx) ht
    rw [heq] at hout
    exact hout (inner.pre_retained_at_surgery c ⟨hc.le, hcd⟩ hT s hsin ht x hx)





theorem duration_ge_of_removal_before_bound
    (outer : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (inner : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) V)
    (hc : 0 < c) (hdB : d ≤ B) (hVU : V ⊆ U) (hV : V.Nonempty)
    (hinitial : ∀ h x, x ∈ V → HEq (inner.forward 0 h x) x)
    (hremove : c < B → SurgeryBallDisappearsAt F outer (origin + c / scale)) :
    d ≤ c := by
  by_contra hnot
  have hcd : c < d := lt_of_not_ge hnot
  exact not_disappears_of_surviving_subcylinder outer inner hc hcd hVU hV hinitial
    (hremove (hcd.trans_le hdB))





theorem stopped_outer_duration_ge_inner
    (outer : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U)
    (inner : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) V)
    (hc : 0 < c) (hdB : d ≤ B) (hVU : V ⊆ U) (hV : V.Nonempty)
    (hinitial : ∀ h x, x ∈ V → HEq (inner.forward 0 h x) x)
    (hstop : c = B ∨ SurgeryBallDisappearsAt F outer (origin + c / scale)) :
    d ≤ c := by
  apply duration_ge_of_removal_before_bound outer inner hc hdB hVU hV hinitial
  intro hcB
  exact hstop.resolve_left (ne_of_lt hcB)

end PoincareConjecture.M44
