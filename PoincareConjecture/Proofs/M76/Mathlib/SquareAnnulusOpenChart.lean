import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusDepth
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusHomeomorph
import PoincareConjecture.Proofs.M76.Mathlib.SquareAnnulusPLLift
import Mathlib.Topology.OpenPartialHomeomorph.Constructions

set_option autoImplicit false

open Set Topology Geometry

namespace PLAnnularStrip

theorem range_annulusMap_open {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    range (fun p : AddCircle (4 * L) × Ioo (-d) d =>
      annulusMap L hL (p.1, p.2)) = depth L ⁻¹' Ioo (-d) d := by
  ext x
  constructor
  · rintro ⟨⟨z, t⟩, rfl⟩
    change depth L (annulusMap L hL (z, t)) ∈ Ioo (-d) d
    rw [depth_annulusMap hL
      (lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (abs_le.mpr ⟨t.property.1.le, t.property.2.le⟩) (by norm_num)) hwidth)]
    exact t.property
  · intro hx
    have hxs : x ∈ squareAnnulus L d :=
      mem_squareAnnulus_iff_depth.mpr ⟨hx.1.le, hx.2.le⟩
    rw [← range_annulusMap hL hd.le hwidth] at hxs
    obtain ⟨⟨z, t⟩, he⟩ := hxs
    have htval : depth L x = (t : ℝ) := by
      rw [← he]
      exact depth_annulusMap hL
        (lt_of_le_of_lt (mul_le_mul_of_nonneg_left (abs_le.mpr t.property)
          (by norm_num)) hwidth) z
    have htopen : (t : ℝ) ∈ Ioo (-d) d := by
      rw [← htval]
      exact hx
    exact ⟨(z, ⟨t, htopen⟩), he⟩

theorem isOpenEmbedding_annulusMap_open {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    IsOpenEmbedding (fun p : AddCircle (4 * L) × Ioo (-d) d =>
      annulusMap L hL (p.1, p.2)) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  have he := (continuous_annulusMap hd.le hwidth).isClosedEmbedding
    (injective_annulusMap hL hwidth)
  refine ⟨he.isEmbedding.comp
    (IsEmbedding.id.prodMap (IsEmbedding.inclusion Ioo_subset_Icc_self)), ?_⟩
  rw [range_annulusMap_open hL hd hwidth]
  exact isOpen_Ioo.preimage (continuous_depth L)

theorem exists_annulus_openPartialHomeomorph {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    ∃ e : OpenPartialHomeomorph (AddCircle (4 * L) × ℝ) (ℝ × ℝ),
      e.source = univ ×ˢ Ioo (-d) d ∧
      (e : (AddCircle (4 * L) × ℝ) → ℝ × ℝ) = annulusMap L hL := by
  let U : Set (AddCircle (4 * L) × ℝ) := univ ×ˢ Ioo (-d) d
  let D : U ≃ₜ AddCircle (4 * L) × Ioo (-d) d :=
    (Homeomorph.Set.prod univ (Ioo (-d) d)).trans
      ((Homeomorph.Set.univ (AddCircle (4 * L))).prodCongr (Homeomorph.refl _))
  have he : IsOpenEmbedding (U.domRestrict (annulusMap L hL)) :=
    (isOpenEmbedding_annulusMap_open hL hd hwidth).comp D.isOpenEmbedding
  have hi : InjOn (annulusMap L hL) U := injOn_iff_injective.mpr he.injective
  exact ⟨OpenPartialHomeomorph.ofContinuousOpenRestrict hi.toPartialEquiv
    (continuousOn_iff_continuous_domRestrict.mpr he.continuous)
    he.isOpenMap (isOpen_univ.prod isOpen_Ioo), rfl, rfl⟩

theorem exists_annulus_PL_openPartialHomeomorph {L d : ℝ}
    (hL : 0 < L) (hd : 0 < d) (hwidth : 4 * d < L) :
    letI : Fact (0 < 4 * L) := ⟨by linarith⟩
    ∃ e : OpenPartialHomeomorph (AddCircle (4 * L) × ℝ) (ℝ × ℝ),
      e.source = univ ×ˢ Ioo (-d) d ∧
      (e : (AddCircle (4 * L) × ℝ) → ℝ × ℝ) = annulusMap L hL ∧
      ∀ a : ℝ, ((AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
        (OpenPartialHomeomorph.refl ℝ)).trans e ∈ piecewiseAffineGroupoid (ℝ × ℝ) := by
  let : Fact (0 < 4 * L) := ⟨by linarith⟩
  obtain ⟨e, heS, heval⟩ := exists_annulus_openPartialHomeomorph hL hd hwidth
  refine ⟨e, heS, heval, ?_⟩
  intro a
  let Q := (AddCircle.openPartialHomeomorphCoe (4 * L) a).prod
    (OpenPartialHomeomorph.refl ℝ)
  apply (mem_piecewiseAffineGroupoid_iff_forward (Q.trans e)).mpr
  have hPL := (locallyPiecewiseAffineOn_annulusMap_lift hL hd hwidth).mono
    (Q.trans e).open_source (fun p hp => by
      have h := hp.2
      rw [heS] at h
      exact ⟨mem_univ _, h.2⟩)
  apply hPL.congr
  intro p _
  change annulusMap L hL ((p.1 : AddCircle (4 * L)), p.2) = e (Q p)
  rw [heval]
  rfl

end PLAnnularStrip
