import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Capping.Collars.FinitePLBallBoundaryCollar
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Products.TwoSideProduct










set_option autoImplicit false

open Set Geometry

private theorem isOpen_relative_union_of_closed_pieces
    {X : Type*} [TopologicalSpace X] {P D A C : Set X}
    (hP : IsClosed P) (hD : IsClosed D)
    (hAC : A ∩ D = C ∩ P)
    (hA : IsOpen ((Subtype.val : P → X) ⁻¹' A))
    (hC : IsOpen ((Subtype.val : D → X) ⁻¹' C)) :
    IsOpen ((Subtype.val : ↥(P ∪ D) → X) ⁻¹' (A ∪ C)) := by
  have hPA : IsClosed (P \ A) := by
    have h := hP.isClosedMap_subtype_val _ hA.isClosed_compl
    convert h using 1
    ext x
    simp
  have hDC : IsClosed (D \ C) := by
    have h := hD.isClosedMap_subtype_val _ hC.isClosed_compl
    convert h using 1
    ext x
    simp
  have heq : (P ∪ D) \ (A ∪ C) = (P \ A) ∪ (D \ C) := by
    ext x
    constructor
    · rintro ⟨hP | hD, hn⟩
      · exact Or.inl ⟨hP, fun ha => hn (Or.inl ha)⟩
      · exact Or.inr ⟨hD, fun hc => hn (Or.inr hc)⟩
    · rintro (⟨hp, hn⟩ | ⟨hd, hn⟩)
      · refine ⟨Or.inl hp, ?_⟩
        rintro (ha | hc)
        · exact hn ha
        · exact hn (hAC.symm.subset ⟨hc, hp⟩).1
      · refine ⟨Or.inr hd, ?_⟩
        rintro (ha | hc)
        · exact hn (hAC.subset ⟨ha, hd⟩).1
        · exact hn hc
  have hclosed : IsClosed ((P ∪ D) \ (A ∪ C)) := heq ▸ hPA.union hDC
  have h := (hclosed.preimage (continuous_subtype_val :
    Continuous (Subtype.val : ↥(P ∪ D) → X))).isOpen_compl
  convert h using 1
  ext x
  change (x : X) ∈ A ∪ C ↔ ¬((x : X) ∈ P ∪ D ∧ (x : X) ∉ A ∪ C)
  simp only [x.property, true_and, not_not]

namespace Set.IsFinitePLBallPair

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "J" => Icc (-1 : ℝ) 1




theorem exists_attachment_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {P D B : Set E} (hD : IsFinitePLBallPair V3 D B) (hP : IsClosed P)
    (hPD : P ∩ D = B) (f : E × ℝ → E)
    (F : (B ×ˢ I : Set (E × ℝ)) ≃ₜ f '' (B ×ˢ I))
    (hF : F.IsFinitePL) (hFval : ∀ z, (F z : E) = f z)
    (hfP : MapsTo f (B ×ˢ I) P)
    (hf0 : ∀ x ∈ B, f (x, 0) = x)
    (hfB : ∀ z ∈ B ×ˢ I, f z ∈ B ↔ z.2 = 0)
    {δ : ℝ} (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2)
    (hopen : ∀ ε : ℝ, 0 < ε → ε ≤ δ →
      IsOpen ((Subtype.val : P → E) ⁻¹' (f '' (B ×ˢ Ico 0 ε)))) :
    ∃ (g σ : E × ℝ → E)
      (H : (B ×ˢ J : Set (E × ℝ)) ≃ₜ ↥((f '' (B ×ˢ I)) ∪ g '' (B ×ˢ I))),
      H.IsFinitePL ∧ (∀ z, (H z : E) = σ z) ∧
      FinitePiecewiseAffineOn g (B ×ˢ I) ∧ MapsTo g (B ×ˢ I) D ∧
      (∀ x ∈ B, g (x, 0) = x) ∧
      (∀ z ∈ B ×ˢ I, g z ∈ B ↔ z.2 = 0) ∧
      (∀ z ∈ B ×ˢ I, σ z = f z) ∧
      (∀ z ∈ B ×ˢ Icc (-1 : ℝ) 0, σ z = g (z.1, -z.2)) ∧
      (∀ x ∈ B, σ (x, 0) = x) ∧
      (∀ z ∈ B ×ˢ J, σ z ∈ B ↔ z.2 = 0) ∧
      ∃ η : ℝ, 0 < η ∧ η ≤ δ ∧
        ∀ ε : ℝ, 0 < ε → ε ≤ η →
          IsOpen ((Subtype.val : ↥(P ∪ D) → E) ⁻¹' (σ '' (B ×ˢ Ioo (-ε) ε))) := by
  classical
  obtain ⟨g, G, hG, hGval, hgD, hg0, hgB, γ, hγ, hγsmall, hgopen⟩ :=
    hD.exists_finitePL_boundary_collar
  have hgPL : FinitePiecewiseAffineOn g (B ×ˢ I) := by
    obtain ⟨g', hg', hG'⟩ := hG
    exact hg'.congr (fun z hz => (hG' ⟨z, hz⟩).symm.trans (hGval ⟨z, hz⟩))
  let U : Bool → Set E := fun b => if b then f '' (B ×ˢ I) else g '' (B ×ˢ I)
  let C : ∀ b, (B ×ˢ I : Set (E × ℝ)) ≃ₜ U b := fun b => Bool.rec G F b
  have hC (b : Bool) : (C b).IsFinitePL := by cases b <;> assumption
  have hbase (b : Bool) (x : E) (hx : x ∈ B) :
      (C b ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩⟩ : E) = x := by
    cases b
    · exact (hGval _).trans (hg0 x hx)
    · exact (hFval _).trans (hf0 x hx)
  have hzero (b : Bool) (z : (B ×ˢ I : Set (E × ℝ))) :
      (C b z : E) ∈ B ↔ (z : E × ℝ).2 = 0 := by
    cases b
    · rw [show (C false z : E) = g z from hGval z]
      exact hgB z z.property
    · rw [show (C true z : E) = f z from hFval z]
      exact hfB z z.property
  have hinter : U true ∩ U false = B := by
    apply Subset.antisymm
    · rintro x ⟨⟨z, hz, rfl⟩, hxg⟩
      exact hPD.subset ⟨hfP hz, by obtain ⟨w, hw, hwz⟩ := hxg; exact hwz ▸ hgD hw⟩
    · intro x hx
      exact ⟨⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩, hf0 x hx⟩,
        ⟨(x, 0), ⟨hx, le_rfl, zero_le_one⟩, hg0 x hx⟩⟩
  obtain ⟨H, hH, hpos, hneg, hH0, hHB⟩ :=
    Homeomorph.exists_two_side_product B U C hC hbase hzero hinter
  have hHcopy := hH
  obtain ⟨σ, hσ, hσval⟩ := hHcopy
  have hpositive (z : E × ℝ) (hz : z ∈ B ×ˢ I) : σ z = f z :=
    (hσval ⟨z, ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩⟩).symm.trans
      ((hpos ⟨z, hz⟩).trans (hFval ⟨z, hz⟩))
  have hnegative (z : E × ℝ) (hz : z ∈ B ×ˢ Icc (-1 : ℝ) 0) :
      σ z = g (z.1, -z.2) :=
    (hσval ⟨z, ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩⟩).symm.trans
      ((hneg ⟨z, hz⟩).trans (hGval _))
  refine ⟨g, σ, H, hH, hσval, hgPL, hgD, hg0, hgB, hpositive, hnegative,
    ?_, ?_, min δ γ, lt_min hδ hγ, min_le_left _ _, ?_⟩
  · intro x hx
    exact (hpositive (x, 0) ⟨hx, le_rfl, zero_le_one⟩).trans (hf0 x hx)
  · intro z hz
    rw [← hσval ⟨z, hz⟩]
    exact hHB ⟨z, hz⟩
  · intro ε hε hεsmall
    have hεδ : ε ≤ δ := hεsmall.trans (min_le_left _ _)
    have hεγ : ε ≤ γ := hεsmall.trans (min_le_right _ _)
    have hεone : ε ≤ 1 := by linarith
    have heq : σ '' (B ×ˢ Ioo (-ε) ε) =
        (f '' (B ×ˢ Ico 0 ε)) ∪ g '' (B ×ˢ Ico 0 ε) := by
      ext x
      constructor
      · rintro ⟨z, hz, rfl⟩
        by_cases ht : 0 ≤ z.2
        · exact Or.inl ⟨z, ⟨hz.1, ht, hz.2.2⟩,
            (hpositive z ⟨hz.1, ht, by linarith [hz.2.2]⟩).symm⟩
        · refine Or.inr ⟨(z.1, -z.2), ⟨hz.1, by linarith, by linarith [hz.2.1]⟩, ?_⟩
          exact (hnegative z ⟨hz.1, by linarith [hz.2.1], by linarith⟩).symm
      · rintro (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
        · exact ⟨z, ⟨hz.1, by linarith [hz.2.1], hz.2.2⟩,
            hpositive z ⟨hz.1, hz.2.1, by linarith [hz.2.2]⟩⟩
        · refine ⟨(z.1, -z.2), ⟨hz.1, by linarith [hz.2.2], by linarith [hz.2.1]⟩, ?_⟩
          simpa only [neg_neg, Prod.eta] using
            hnegative (z.1, -z.2) ⟨hz.1, by linarith [hz.2.2], by linarith [hz.2.1]⟩
    rw [heq]
    have hsub : B ×ˢ Ico 0 ε ⊆ B ×ˢ I :=
      fun z hz => ⟨hz.1, hz.2.1, hz.2.2.le.trans hεone⟩
    apply isOpen_relative_union_of_closed_pieces hP hD.isCompact.isClosed
      ?_
      (hopen ε hε hεδ) (hgopen ε hε hεγ)
    have hfend : (f '' (B ×ˢ Ico 0 ε)) ∩ D = B := by
      apply Subset.antisymm
      · rintro x ⟨⟨z, hz, rfl⟩, hxd⟩
        exact hPD.subset ⟨hfP (hsub hz), hxd⟩
      · intro x hx
        exact ⟨⟨(x, 0), ⟨hx, le_rfl, hε⟩, hf0 x hx⟩, hD.1 hx⟩
    have hgend : (g '' (B ×ˢ Ico 0 ε)) ∩ P = B := by
      apply Subset.antisymm
      · rintro x ⟨⟨z, hz, rfl⟩, hxp⟩
        exact hPD.subset ⟨hxp, hgD (hsub hz)⟩
      · intro x hx
        exact ⟨⟨(x, 0), ⟨hx, le_rfl, hε⟩, hg0 x hx⟩, (hPD.symm.subset hx).1⟩
    exact hfend.trans hgend.symm

end Set.IsFinitePLBallPair
