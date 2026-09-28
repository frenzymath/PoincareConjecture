import PoincareConjecture.Proofs.M76.Mathlib.CenteredAnnulusMap











set_option autoImplicit false

open Set Geometry

namespace PLAnnularStrip




theorem exists_centeredAnnulus_openPartialHomeomorph {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ e : OpenPartialHomeomorph (AddCircle (4 * L) × ℝ) (ℝ × ℝ),
      e.source = univ ×ˢ Ioo (-d) d ∧
      (e : (AddCircle (4 * L) × ℝ) → ℝ × ℝ) = centeredAnnulusMap L hL := by
  obtain ⟨e, heS, heval⟩ := exists_annulus_openPartialHomeomorph hL hd hwidth
  let A : (AddCircle (4 * L) × ℝ) ≃ₜ (AddCircle (4 * L) × ℝ) :=
    (Homeomorph.addLeft ((L / 2 : ℝ) : AddCircle (4 * L))).prodCongr (Homeomorph.refl ℝ)
  let B : (ℝ × ℝ) ≃ₜ (ℝ × ℝ) :=
    (ContinuousAffineEquiv.constVAdd ℝ (ℝ × ℝ) (-(L / 2), 0)).toHomeomorph
  let C := A.toOpenPartialHomeomorph.trans (e.trans B.toOpenPartialHomeomorph)
  refine ⟨C, ?_, ?_⟩
  · ext p
    change (p ∈ univ ∧ A p ∈ e.source ∧ e (A p) ∈ univ) ↔
      p ∈ univ ×ˢ Ioo (-d) d
    rw [heS]
    simp only [mem_univ, true_and, and_true, mem_prod]
    rfl
  · funext p
    change B (e (A p)) = centeredAnnulusMap L hL p
    rw [heval]
    change (-(L / 2) +
        (annulusMap L hL ((((L / 2 : ℝ) : AddCircle (4 * L)) + p.1), p.2)).1,
        0 + (annulusMap L hL ((((L / 2 : ℝ) : AddCircle (4 * L)) + p.1), p.2)).2) = _
    simp only [centeredAnnulusMap, zero_add, sub_eq_add_neg, add_comm]




theorem exists_centeredAnnulus_PL_openPartialHomeomorph {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    ∃ e : OpenPartialHomeomorph (AddCircle (4 * L) × ℝ) (ℝ × ℝ),
      e.source = univ ×ˢ Ioo (-d) d ∧
      (e : (AddCircle (4 * L) × ℝ) → ℝ × ℝ) = centeredAnnulusMap L hL ∧
      ∀ a : ℝ, ((AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
        (OpenPartialHomeomorph.refl ℝ)).trans e ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨e, heS, heval⟩ := exists_centeredAnnulus_openPartialHomeomorph hL hd hwidth
  refine ⟨e, heS, heval, ?_⟩
  intro a
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  apply (mem_piecewiseAffineGroupoid_iff_forward (Q.trans e)).mpr
  have hPL := (locallyPiecewiseAffineOn_centeredAnnulusMap_lift hL hd hwidth).mono
    (Q.trans e).open_source (fun p hp => by
      have h := hp.2
      rw [heS] at h
      exact ⟨mem_univ _, h.2⟩)
  apply hPL.congr
  intro p _
  change centeredAnnulusMap L hL ((p.1 : AddCircle (4 * L)), p.2) = e (Q p)
  rw [heval]
  rfl

end PLAnnularStrip
