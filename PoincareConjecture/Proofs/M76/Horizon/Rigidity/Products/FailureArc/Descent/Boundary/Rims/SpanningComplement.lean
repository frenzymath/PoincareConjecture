import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Rims.EdgeInterval
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.Mathlib.OriginalRimComplement



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

theorem spanning_original_rim_complement
    {T Q S K L : Set P2} (hT : IsFinitePLBallPair P2 T Q) (hQS : Q ⊆ S)
    (c : Bool → P2 → P2)
    (hQ : ∀ i z, z ∈ source → (c i z ∈ Q ↔ z.1 = 0))
    (hKL : Disjoint K L)
    (hcover : (c false '' source ∪ c true '' source) ∪ (K ∪ L) = S)
    (sign : Bool → Bool)
    (hcontact : ∀ i, K ∩ (c i '' source) = c i '' arm (farArmParameter (sign i)))
    (H : Sq ≃ₜ K) (hH : H.IsFinitePL)
    (hHQ : ∀ z : Sq, (H z : P2) ∈ Q ↔ (z : P2).2 = 0)
    (hleft : ∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (sign false)))
    (hright : ∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (sign true))) :
    let a := c false (0, farArmParameter (sign false))
    let b := c true (0, farArmParameter (sign true))
    let V := (L ∩ Q) ∪ (c false '' stripEnd 0 ∪ c true '' stripEnd 0)
    a ≠ b ∧ IsFinitePLBallPair ℝ V {a, b} ∧
      (K ∩ Q) ∪ V = Q ∧ (K ∩ Q) ∩ V = {a, b} ∧
      ∃ q : I ≃ₜ (K ∩ Q : Set P2), q.IsFinitePL ∧
        ∀ t : I, (q t : P2) = H ⟨(t, 0), t.property, by norm_num⟩ := by
  let a := c false (0, farArmParameter (sign false))
  let b := c true (0, farArmParameter (sign true))
  let U := K ∩ Q
  let V := (L ∩ Q) ∪ (c false '' stripEnd 0 ∪ c true '' stripEnd 0)
  have hfar (i : Bool) : farArmParameter (sign i) ∈ Icc (-1 : ℝ) 1 := by
    cases sign i <;> norm_num [farArmParameter]
  have hl : (H ⟨(0, 0), by norm_num, by norm_num⟩ : P2) = a := hleft 0
  have hr : (H ⟨(1, 0), by norm_num, by norm_num⟩ : P2) = b := hright 0
  have hab : a ≠ b := by
    intro he
    have hh := H.injective (Subtype.ext (hl.trans (he.trans hr.symm)))
    have hf := congrArg (fun z : Sq ↦ (z : P2).1) hh
    norm_num at hf
  obtain ⟨hU, q, hq, hqval⟩ := exists_marked_square_rim_interval H hH hHQ
  rw [hl, hr] at hU
  have hend (i : Bool) : (c i '' source) ∩ Q = c i '' stripEnd 0 := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzQ⟩
      exact ⟨z, ⟨(hQ i z hz).mp hzQ, hz.2⟩, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      have hzS : z ∈ source := stripEnd_subset_source (0 : I) hz
      exact ⟨⟨z, hzS, rfl⟩, (hQ i z hzS).mpr hz.1⟩
  have harm (i : Bool) : (c i '' arm (farArmParameter (sign i))) ∩ Q =
      {c i (0, farArmParameter (sign i))} := by
    ext x
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hzQ⟩
      have hzS : z ∈ source := ⟨hz.1, hz.2.symm ▸ hfar i⟩
      have hz0 := (hQ i z hzS).mp hzQ
      exact congrArg (c i) (Prod.ext hz0 hz.2)
    · rintro rfl
      exact ⟨⟨(0, farArmParameter (sign i)), ⟨by norm_num, rfl⟩, rfl⟩,
        (hQ i _ ⟨by norm_num, hfar i⟩).mpr rfl⟩
  have huv : U ∪ V = Q := by
    ext x
    constructor
    · rintro (hx | hx | hx | hx)
      · exact hx.2
      · exact hx.2
      · exact ((hend false).symm.subset hx).2
      · exact ((hend true).symm.subset hx).2
    · intro hx
      rcases hcover.symm.subset (hQS hx) with (hx0 | hx1) | hxK | hxL
      · exact Or.inr (Or.inr (Or.inl ((hend false).subset ⟨hx0, hx⟩)))
      · exact Or.inr (Or.inr (Or.inr ((hend true).subset ⟨hx1, hx⟩)))
      · exact Or.inl ⟨hxK, hx⟩
      · exact Or.inr (Or.inl ⟨hxL, hx⟩)
  have hinter : U ∩ V = {a, b} := by
    ext x
    constructor
    · rintro ⟨hxU, hxL | hx0 | hx1⟩
      · exact (disjoint_left.mp hKL hxU.1 hxL.1).elim
      · exact Or.inl ((harm false).subset
          ⟨(hcontact false).subset ⟨hxU.1, ((hend false).symm.subset hx0).1⟩, hxU.2⟩)
      · exact Or.inr ((harm true).subset
          ⟨(hcontact true).subset ⟨hxU.1, ((hend true).symm.subset hx1).1⟩, hxU.2⟩)
    · rintro (rfl | rfl)
      · exact ⟨hU.1 (Or.inl rfl), Or.inr (Or.inl
          ⟨(0, farArmParameter (sign false)), ⟨rfl, hfar false⟩, rfl⟩)⟩
      · exact ⟨hU.1 (Or.inr rfl), Or.inr (Or.inr
          ⟨(0, farArmParameter (sign true)), ⟨rfl, hfar true⟩, rfl⟩)⟩
  obtain ⟨W, hW, hUW, hiW⟩ := hT.exists_boundary_arc_complement hU inter_subset_right hab
  have hWV : W = V := by
    apply Subset.antisymm
    · intro x hx
      rcases huv.symm.subset (hUW.subset (Or.inr hx)) with hxU | hxV
      · exact (hinter.symm.subset (hiW.subset ⟨hxU, hx⟩)).2
      · exact hxV
    · intro x hx
      rcases hUW.symm.subset (huv.subset (Or.inr hx)) with hxU | hxW
      · exact (hiW.symm.subset (hinter.subset ⟨hxU, hx⟩)).2
      · exact hxW
  refine ⟨hab, ?_, huv, hinter, q, hq, hqval⟩
  simpa only [hWV] using hW

end PoincareConjecture.M76.Dehn
