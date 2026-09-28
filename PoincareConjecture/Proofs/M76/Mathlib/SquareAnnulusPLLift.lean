import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonPLAtlasNeighborhood

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

theorem finitePiecewiseAffineOn_annulusMap_period {L d c : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L)
    (hc : (c : AddCircle (4 * L)) = 0) :
    FinitePiecewiseAffineOn
      (fun p : ℝ × ℝ => annulusMap L hL ((p.1 : AddCircle (4 * L)), p.2))
      (Icc c (c + 4 * L) ×ˢ Icc (-d) d) := by
  let a : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (c, 0)
  have h := (finitePiecewiseAffineOn_wrappedStripMap hd hwidth).precomp_affineEquiv a.symm
  rw [ContinuousAffineEquiv.symm_symm] at h
  have himage : a '' rectangle (4 * L) d = Icc c (c + 4 * L) ×ˢ Icc (-d) d := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      change c + q.1 ∈ Icc c (c + 4 * L) ∧ 0 + q.2 ∈ Icc (-d) d
      exact ⟨by constructor <;> linarith [hq.1.1, hq.1.2], by simpa using hq.2⟩
    · intro hp
      refine ⟨(p.1 - c, p.2), ⟨?_, hp.2⟩, ?_⟩
      · constructor <;> linarith [hp.1.1, hp.1.2]
      · change (c + (p.1 - c), 0 + p.2) = p
        exact Prod.ext (by ring) (zero_add _)
  rw [← himage]
  apply h.congr
  rintro _ ⟨p, hp, rfl⟩
  simp only [Function.comp_apply, ContinuousAffineEquiv.symm_apply_apply]
  change wrappedStripMap L p =
    annulusMap L hL ((((c + p.1 : ℝ) : AddCircle (4 * L))), 0 + p.2)
  rw [AddCircle.coe_add, hc, zero_add, zero_add]
  exact (annulusMap_coe hL
    (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr hp.2)
      (by norm_num)) hwidth) hp.1).symm

theorem finitePiecewiseAffineOn_annulusMap_twoPeriods {L d c : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L)
    (hc : (c : AddCircle (4 * L)) = 0) :
    FinitePiecewiseAffineOn
      (fun p : ℝ × ℝ => annulusMap L hL ((p.1 : AddCircle (4 * L)), p.2))
      (Icc (c - 4 * L) (c + 4 * L) ×ˢ Icc (-d) d) := by
  have hc' : ((c - 4 * L : ℝ) : AddCircle (4 * L)) = 0 := by
    rw [AddCircle.coe_sub, hc, AddCircle.coe_period, sub_zero]
  have hleft := finitePiecewiseAffineOn_annulusMap_period hL hd hwidth hc'
  rw [sub_add_cancel] at hleft
  have hright := finitePiecewiseAffineOn_annulusMap_period hL hd hwidth hc
  have h := finitePiecewiseAffineOn_union hleft hright
  rw [← union_prod, Icc_union_Icc_eq_Icc (by linarith) (by linarith)] at h
  exact h

theorem locallyPiecewiseAffineOn_annulusMap_lift {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    LocallyPiecewiseAffineOn
      (fun p : ℝ × ℝ => annulusMap L hL ((p.1 : AddCircle (4 * L)), p.2))
      (univ ×ˢ Ioo (-d) d) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  apply LocallyPiecewiseAffineOn.locality
  intro p hp
  let r : ℝ := AddCircle.equivIco (4 * L) 0 (p.1 : AddCircle (4 * L))
  have hr : r ∈ Ico 0 (4 * L) := by
    simpa only [zero_add] using
      (AddCircle.equivIco (4 * L) 0 (p.1 : AddCircle (4 * L))).property
  have hrcoe : (r : AddCircle (4 * L)) = (p.1 : AddCircle (4 * L)) :=
    AddCircle.coe_equivIco
  let c := p.1 - r
  have hc : (c : AddCircle (4 * L)) = 0 := by
    change ((p.1 - r : ℝ) : AddCircle (4 * L)) = 0
    rw [AddCircle.coe_sub, hrcoe, sub_self]
  let S := Icc (c - 4 * L) (c + 4 * L) ×ˢ Icc (-d) d
  have hpS : p ∈ interior S := by
    change p ∈ interior (Icc (c - 4 * L) (c + 4 * L) ×ˢ Icc (-d) d)
    rw [interior_prod_eq, interior_Icc, interior_Icc]
    exact ⟨⟨by dsimp [c]; linarith [hr.1], by dsimp [c]; linarith [hr.2]⟩, hp.2⟩
  refine ⟨interior S, hpS, ?_⟩
  have hPL := finitePiecewiseAffineOn_annulusMap_twoPeriods hL hd hwidth hc
  exact hPL.locallyPiecewiseAffineOn_of_subset_interior
    ((isOpen_univ.prod isOpen_Ioo).inter isOpen_interior) inter_subset_right

end PLAnnularStrip
