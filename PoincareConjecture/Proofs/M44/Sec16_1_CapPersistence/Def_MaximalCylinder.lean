import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_CylinderUnion











set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M44




theorem exists_maximal_based_cylinder
    {F : SurgeryFlowData.{u}} {origin scale b0 B : ℝ}
    {U : Set (F.slice origin).carrier}
    (e0 : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 b0) U)
    (hb0 : 0 < b0) (hbB : b0 ≤ B)
    (hinitial : ∀ h x, x ∈ U → HEq (e0.forward 0 h x) x) :
    ∃ c : ℝ, 0 < c ∧ c ≤ B ∧
      ∃ E : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 c) U,
        (∀ h x, x ∈ U → HEq (E.forward 0 h x) x) ∧
        (∀ s (hs : s ∈ Ico 0 b0) (hs' : s ∈ Ico 0 c), ∀ x ∈ U,
          E.forward s hs' x = e0.forward s hs x) ∧
        ∀ d : ℝ, c < d → d ≤ B →
          ¬ ∃ E' : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 d) U,
            ∀ h x, x ∈ U → HEq (E'.forward 0 h x) x := by
  classical
  let S : Set ℝ := {b | 0 < b ∧ b ≤ B ∧
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 b) U,
      ∀ h x, x ∈ U → HEq (e.forward 0 h x) x}
  have hb0S : b0 ∈ S := ⟨hb0, hbB, e0, hinitial⟩
  have hne : S.Nonempty := ⟨b0, hb0S⟩
  have hbounded : BddAbove S := ⟨B, fun _ hb => hb.2.1⟩
  let c := sSup S
  have hb0c : b0 ≤ c := le_csSup hbounded hb0S
  have hc : 0 < c := hb0.trans_le hb0c
  have hcB : c ≤ B := csSup_le hne (fun _ hb => hb.2.1)
  let family (i : S) : SurgeryFlowCylinder F (F.slice origin) origin scale (Ico 0 i.1) U :=
    Classical.choose i.2.2.2
  have hfamily (i : S) : ∀ h x, x ∈ U → HEq ((family i).forward 0 h x) x :=
    Classical.choose_spec i.2.2.2
  have hcover : ∀ s ∈ Ico 0 c, ∃ i : S, s < i.1 := by
    intro s hs
    obtain ⟨b, hb, hsb⟩ := exists_lt_of_lt_csSup hne hs.2
    exact ⟨⟨b, hb⟩, hsb⟩
  have hinit : ∀ i j : S, ∀ (hi : 0 < i.1) (hj : 0 < j.1), ∀ x ∈ U,
      (family i).forward 0 ⟨le_rfl, hi⟩ x = (family j).forward 0 ⟨le_rfl, hj⟩ x := by
    intro i j hi hj x hx
    exact eq_of_heq ((hfamily i _ x hx).trans (hfamily j _ x hx).symm)
  obtain ⟨E, hagree⟩ := exists_cylinder_of_coverage (fun i : S => i.1) family hc hcover hinit
  have hEinitial : ∀ h x, x ∈ U → HEq (E.forward 0 h x) x := by
    intro h x hx
    rw [hagree ⟨b0, hb0S⟩ 0 ⟨le_rfl, hb0⟩ h x hx]
    exact hfamily _ _ x hx
  refine ⟨c, hc, hcB, E, hEinitial, ?_, ?_⟩
  · intro s hs hs' x hx
    apply cylinder_forward_eq_of_initial E e0 hs.1
      (fun _ ht => ⟨ht.1, ht.2.trans_lt hs'.2⟩)
      (fun _ ht => ⟨ht.1, ht.2.trans_lt hs.2⟩) x hx hx
    exact eq_of_heq ((hEinitial _ x hx).trans (hinitial _ x hx).symm)
  · intro d hcd hdB hext
    have hdS : d ∈ S := ⟨hc.trans hcd, hdB, hext⟩
    exact (not_lt_of_ge (le_csSup hbounded hdS)) hcd

end PoincareConjecture.M44
