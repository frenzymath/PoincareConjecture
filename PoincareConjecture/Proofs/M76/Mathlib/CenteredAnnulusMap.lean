import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusOpenChart

set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip

noncomputable def centeredAnnulusMap (L : ℝ) (hL : 0 < L)
    (p : AddCircle (4 * L) × ℝ) : ℝ × ℝ :=
  let q := annulusMap L hL ((((L / 2 : ℝ) : AddCircle (4 * L)) + p.1), p.2)
  (q.1 - L / 2, q.2)

theorem centeredAnnulusMap_core {L d s t : ℝ}
    (hL : 0 < L) (hwidth : 4 * d < L) (hcore : 6 * d ≤ L)
    (hs : |s| ≤ d) (ht : |t| ≤ d) :
    centeredAnnulusMap L hL ((s : AddCircle (4 * L)), t) = (s, t) := by
  have hsmall : 4 * |t| < L :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left ht (by norm_num)) hwidth
  have hleft : 2 * |t| ≤ L / 2 + s := by
    linarith [(abs_le.mp hs).1]
  have hright : 2 * |t| ≤ L - (L / 2 + s) := by
    linarith [(abs_le.mp hs).2]
  unfold centeredAnnulusMap
  rw [← AddCircle.coe_add, annulusMap_middle hL hsmall hleft hright]
  exact Prod.ext (by dsimp; ring) rfl

theorem locallyPiecewiseAffineOn_centeredAnnulusMap_lift {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    LocallyPiecewiseAffineOn
      (fun p : ℝ × ℝ => centeredAnnulusMap L hL ((p.1 : AddCircle (4 * L)), p.2))
      (univ ×ˢ Ioo (-d) d) := by
  let U : Set (ℝ × ℝ) := univ ×ˢ Ioo (-d) d
  let A : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (L / 2, 0)
  let B : (ℝ × ℝ) ≃ᴬ[ℝ] (ℝ × ℝ) :=
    ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-(L / 2), 0)
  have hU : IsOpen U := isOpen_univ.prod isOpen_Ioo
  have hA := locallyPiecewiseAffineOn_affine A.toContinuousAffineMap hU
  have hcomp := (locallyPiecewiseAffineOn_annulusMap_lift hL hd hwidth).comp hA
  have hsource : U ⊆ U ∩ A ⁻¹' U := by
    intro p hp
    refine ⟨hp, mem_univ _, ?_⟩
    change 0 + p.2 ∈ Ioo (-d) d
    simpa only [zero_add] using hp.2
  have hcomp' := hcomp.mono hU hsource
  have hB := locallyPiecewiseAffineOn_affine B.toContinuousAffineMap isOpen_univ
  have hfinal := (hB.comp hcomp').mono hU (fun p hp => ⟨hp, mem_univ _⟩)
  apply hfinal.congr
  intro p _
  change (-(L / 2) +
      (annulusMap L hL ((((L / 2 + p.1 : ℝ) : AddCircle (4 * L))), 0 + p.2)).1,
      0 + (annulusMap L hL ((((L / 2 + p.1 : ℝ) : AddCircle (4 * L))), 0 + p.2)).2) = _
  simp only [AddCircle.coe_add, zero_add, add_zero, centeredAnnulusMap,
    sub_eq_add_neg, add_comm]

end PLAnnularStrip
