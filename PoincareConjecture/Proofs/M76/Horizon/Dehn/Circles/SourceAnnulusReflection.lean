import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.SourceAnnulusPeriod
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusFinitePL









set_option autoImplicit false

open Set Geometry PLAnnularStrip

namespace Dehn

theorem exists_square_annulus_depth_reflection {L d : ℝ}
    (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ r : squareAnnulus L d ≃ₜ squareAnnulus L d, r.IsFinitePL ∧
      (∀ p, depth L (r p) = -depth L p) ∧
      ∀ (s : ℝ) (_hs : s ∈ Icc 0 (4 * L)) (u : Icc (-d) d),
        (r ⟨annulusMap L (by linarith) ((s : AddCircle (4 * L)), u),
          annulus_period_point_mem hd hwidth _ u⟩ : ℝ × ℝ) =
          annulusMap L (by linarith) ((s : AddCircle (4 * L)), -(u : ℝ)) := by
  let h : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ) :=
    (ContinuousLinearEquiv.refl ℝ ℝ).prodCongr (ContinuousLinearEquiv.neg ℝ)
  have hh (x : ℝ × ℝ) : h x = (x.1, -x.2) := rfl
  have hhs (x : ℝ × ℝ) : h.symm x = (x.1, -x.2) := rfl
  have him : h.symm '' rectangle (4 * L) d = rectangle (4 * L) d := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨hy.1, ?_⟩
      change -y.2 ∈ Icc (-d) d
      constructor <;> linarith [hy.2.1, hy.2.2]
    · intro hx
      refine ⟨h x, ⟨hx.1, ?_⟩, h.symm_apply_apply x⟩
      change -x.2 ∈ Icc (-d) d
      constructor <;> linarith [hx.2.1, hx.2.2]
  let φ : (ℝ × ℝ) → (ℝ × ℝ) := wrappedStripMap L ∘ h
  have hφ : FinitePiecewiseAffineOn φ (rectangle (4 * L) d) := by
    have hf := (finitePiecewiseAffineOn_wrappedStripMap hd hwidth).precomp_affineEquiv
      h.toContinuousAffineEquiv
    change FinitePiecewiseAffineOn φ (h.symm '' rectangle (4 * L) d) at hf
    simpa only [him] using hf
  have hval (x : ℝ × ℝ) (hx : x ∈ rectangle (4 * L) d) :
      φ x = annulusMap L (by linarith) ((x.1 : AddCircle (4 * L)), -x.2) := by
    have hn : 4 * |-x.2| < L := by
      rw [abs_neg]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (abs_le.mpr hx.2) (by norm_num)) hwidth
    exact (annulusMap_coe (by linarith) hn hx.1).symm
  have hneg {x : ℝ} (hx : x ∈ Icc (-d) d) : -x ∈ Icc (-d) d := by
    constructor <;> linarith [hx.1, hx.2]
  have hfib : ∀ x ∈ rectangle (4 * L) d, ∀ y ∈ rectangle (4 * L) d,
      φ x = φ y ↔ x.2 = y.2 ∧
        (x.1 : AddCircle (4 * L)) = (y.1 : AddCircle (4 * L)) := by
    intro x hx y hy
    rw [hval x hx, hval y hy]
    constructor
    · intro he
      have he' := injective_annulusMap (by linarith : 0 < L) hwidth
        (a₁ := ((x.1 : AddCircle (4 * L)), ⟨-x.2, hneg hx.2⟩))
        (a₂ := ((y.1 : AddCircle (4 * L)), ⟨-y.2, hneg hy.2⟩)) he
      exact ⟨neg_injective (congrArg (fun p => (p.2 : ℝ)) he'), congrArg Prod.fst he'⟩
    · rintro ⟨hu, hs⟩
      rw [hu, hs]
  have hrange : φ '' rectangle (4 * L) d = squareAnnulus L d := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hval x hx]
      exact annulus_period_point_mem hd hwidth _ ⟨-x.2, hneg hx.2⟩
    · intro hp
      obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth ⟨p, hp⟩
      have hu := mem_squareAnnulus_iff_depth.mp hp
      refine ⟨(s, -depth L p), ⟨hs, hneg hu⟩, ?_⟩
      rw [hval _ ⟨hs, hneg hu⟩, neg_neg]
      exact hsp.symm
  obtain ⟨c, hc, _, hperiod, hpoint⟩ :=
    exists_finitePL_annulus_of_periodic_strip hd hwidth φ hφ hfib
  let r := c.trans (Homeomorph.setCongr hrange)
  have hr : r.IsFinitePL := by
    obtain ⟨f, hf, hcf⟩ := hc
    exact ⟨f, hf, hcf⟩
  refine ⟨r, hr, ?_, ?_⟩
  · intro p
    obtain ⟨s, hs, hsp⟩ := exists_period_parameter_of_depth hd hwidth p
    change depth L (c p) = -depth L p
    rw [hpoint p s hs hsp, hval _ ⟨hs, mem_squareAnnulus_iff_depth.mp p.property⟩]
    apply depth_annulusMap (by linarith)
    rw [abs_neg]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr
      (mem_squareAnnulus_iff_depth.mp p.property)) (by norm_num)) hwidth
  · intro s hs u
    exact (hperiod s hs u).trans (hval _ ⟨hs, u.property⟩)

end Dehn
