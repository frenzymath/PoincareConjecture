import PoincareConjecture.Proofs.M47.BlowupControlsCapClock









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.M47



theorem exists_cap_birth_cylinder_terminal_map
    {F : SurgeryFlowData.{u}} {C : GeneralizedSliceCarrier.{u}}
    {origin Q a : ℝ} {U : Set C.carrier}
    (E : SurgeryFlowCylinder F C origin Q (Icc a 0) U)
    (hU : IsOpen U) (ha : a < 0) (h : ℝ) (hh : 0 < h) :
    let t := origin + a / Q
    let V := E.forward a ⟨le_rfl, ha.le⟩ '' U
    let d := (origin - t) / h ^ 2
    0 < d ∧
      ∃ f : SurgeryFlowCylinder F (F.slice t) t (h⁻¹ ^ 2) (Icc 0 d) V,
        (∀ hs x, x ∈ V → HEq (f.forward 0 hs x) x) ∧
        ∀ hd hz x, x ∈ U →
          HEq (f.forward d hd (E.forward a ⟨le_rfl, ha.le⟩ x))
            (E.forward 0 hz x) := by
  dsimp only
  have hQ := E.scale_pos
  have hd : 0 < (origin - (origin + a / Q)) / h ^ 2 := by
    apply div_pos _ (sq_pos_of_pos hh)
    linarith only [div_neg_of_neg_of_pos ha hQ]
  obtain ⟨hmem, f, based, hpoint⟩ := exists_cap_birth_cylinder E hU ha h hh
  refine ⟨hd, f, based, ?_⟩
  intro htop hzero x hx
  let d := (origin - (origin + a / Q)) / h ^ 2
  have hparameter : a + Q * d * h ^ 2 = 0 := by
    dsimp only [d]
    field_simp [hQ.ne', hh.ne']
    ring
  have hterminal (s : ℝ) (hs : s ∈ Icc a 0) (hs0 : s = 0) :
      HEq (E.forward s hs x) (E.forward 0 hzero x) := by
    subst s
    rfl
  exact (Sigma.mk.inj (hpoint d htop x hx)).2.trans
    (hterminal _ (hmem htop) hparameter)

end PoincareConjecture.M47
