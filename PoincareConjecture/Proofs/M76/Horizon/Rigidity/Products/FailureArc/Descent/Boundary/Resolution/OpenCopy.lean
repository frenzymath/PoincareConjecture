import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Pasting.RetainedCopy
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.ComponentRetention
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Retention.OpenSourceCopy



set_option autoImplicit false
open Set Geometry PLAnnularStrip

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "I" => Icc (0 : ℝ) 1
local notation "Sq" => (I ×ˢ I : Set P2)

private theorem compact_of_square_chart {K : Set P2} (H : Sq ≃ₜ K) : IsCompact K := by
  let : CompactSpace Sq := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
  have hrange : range (fun z : Sq ↦ (H z : P2)) = K := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact (H z).property
    · intro hx
      exact ⟨H.symm ⟨x, hx⟩, congrArg Subtype.val (H.apply_symm_apply _)⟩
  rw [← hrange]
  exact isCompact_range (continuous_subtype_val.comp H.continuous)

theorem AnnulusSquareCopies.isCompact_piece
    {X : Type*} {f : Fin 2 → P2 → X} {g : P2 → X}
    (C : AnnulusSquareCopies f g) (i : Fin 2) : IsCompact (C.piece i) :=
  compact_of_square_chart (C.chart i)

theorem AnnulusSquareCopies.isCompact_source
    {X : Type*} {f : Fin 2 → P2 → X} {g : P2 → X}
    (C : AnnulusSquareCopies f g) : IsCompact (squareAnnulus 8 1) := by
  rw [← C.cover]
  exact (C.isCompact_piece 0).union (C.isCompact_piece 1)

theorem exists_spanning_resolution_open_copy
    {X : Type*} {S K L : Set P2} {old g : P2 → X} {τ : C3 → X}
    (c : Bool → P2 → P2)
    (hc : ∀ i, ContinuousOn (c i) source) (hcS : ∀ i, MapsTo (c i) source S)
    (hci : ∀ i, InjOn (c i) source)
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, old (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, old (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : S ∩ old ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (H : Sq ≃ₜ K) (hL : IsClosed L) (hKS : K ⊆ S) (hKL : Disjoint K L)
    (hcover : (c false '' source ∪ c true '' source) ∪ (K ∪ L) = S)
    (sign : Bool → Bool)
    (hcontact : ∀ i, K ∩ (c i '' source) = c i '' arm (farArmParameter (sign i)))
    (hleft : ∀ t : I, (H ⟨(0, t), by norm_num, t.property⟩ : P2) =
      c false (t, farArmParameter (sign false)))
    (hright : ∀ t : I, (H ⟨(1, t), by norm_num, t.property⟩ : P2) =
      c true (t, farArmParameter (sign true)))
    {f : Fin 2 → P2 → X} (C : AnnulusSquareCopies f g)
    (hval : ∀ z : Sq, f 0 z = old (H z))
    (hdouble : {x : P2 | x ∈ squareAnnulus 8 1 ∧
        ∃ y ∈ squareAnnulus 8 1, y ≠ x ∧ g y = g x} =
      (fun z : Sq ↦ (C.chart 0 z : P2)) ''
        {u : Sq | ∃ v : Sq, v ≠ u ∧ old (H v) = old (H u)}) :
    ∃ (U V : Set P2) (J : U ≃ₜ V),
      U ⊆ K ∧ V ⊆ squareAnnulus 8 1 ∧
      IsOpen ((Subtype.val : S → P2) ⁻¹' U) ∧
      IsOpen ((Subtype.val : squareAnnulus 8 1 → P2) ⁻¹' V) ∧
      (∀ x : U, ∃ hx : (x : P2) ∈ K,
        (J x : P2) = C.retainedDiskCopy H ⟨x, hx⟩) ∧
      (∀ x : U, g (J x) = old x) ∧
      (∀ x : K, (x : P2) ∈ doubleLocusOn old S → (x : P2) ∈ U) ∧
      doubleLocusOn g (squareAnnulus 8 1) ⊆ V := by
  let B := (c false '' source ∪ c true '' source) ∪ L
  have hB : IsClosed B := by
    have hs : IsCompact source := isCompact_Icc.prod isCompact_Icc
    exact ((hs.image_of_continuousOn (hc false)).isClosed.union
      (hs.image_of_continuousOn (hc true)).isClosed).union hL
  apply Annuli.exists_retained_open_source_copy hKS (compact_of_square_chart H)
    hB (compact_of_square_chart (C.chart 1)).isClosed
    (C.retainedDiskCopy H) (C.retainedDiskCopy_injective H)
    (C.retainedDiskCopy_continuous H)
  · intro x
    exact C.chart_mem 0 (H.symm x)
  · intro x
    change g (C.chart 0 (H.symm x)) = old x
    rw [C.val, hval, Homeomorph.apply_symm_apply]
  · intro x hx
    rcases hcover.symm.subset hx with hx | hx | hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inl hx
    · exact Or.inr (Or.inr hx)
  · intro x hx
    rcases C.cover.symm.subset hx with hx | hx
    · let z := (C.chart 0).symm ⟨x, hx⟩
      refine Or.inl ⟨H z, ?_⟩
      simp only [AnnulusSquareCopies.retainedDiskCopy, Homeomorph.symm_apply_apply]
      exact congrArg Subtype.val ((C.chart 0).apply_symm_apply _)
    · exact Or.inr hx
  · intro x hx
    obtain ⟨v, hv⟩ := (C.chart 1).surjective ⟨C.retainedDiskCopy H x, hx⟩
    have hcross := (C.cross (H.symm x) v).mp (congrArg Subtype.val hv).symm
    let z := H.symm x
    have hHx : (H z : P2) = x := congrArg Subtype.val (H.apply_symm_apply x)
    have hside : ∃ i, (x : P2) ∈ c i '' source := by
      rcases hcross.2 with hz | hz
      · have he : z = ⟨(0, z.val.2), by norm_num, z.property.2⟩ :=
          Subtype.ext (Prod.ext hz rfl)
        have hx' : (x : P2) = c false (z.val.2, farArmParameter (sign false)) := by
          exact hHx.symm.trans ((congrArg (fun w : Sq ↦ (H w : P2)) he).trans
            (hleft ⟨z.val.2, z.property.2⟩))
        exact ⟨false, ⟨_, ⟨z.property.2, by
          cases sign false <;> norm_num [farArmParameter]⟩, hx'.symm⟩⟩
      · have he : z = ⟨(1, z.val.2), by norm_num, z.property.2⟩ :=
          Subtype.ext (Prod.ext hz rfl)
        have hx' : (x : P2) = c true (z.val.2, farArmParameter (sign true)) := by
          exact hHx.symm.trans ((congrArg (fun w : Sq ↦ (H w : P2)) he).trans
            (hright ⟨z.val.2, z.property.2⟩))
        exact ⟨true, ⟨_, ⟨z.property.2, by
          cases sign true <;> norm_num [farArmParameter]⟩, hx'.symm⟩⟩
    obtain ⟨i, hi⟩ := hside
    cases i
    · exact Or.inl (Or.inl hi)
    · exact Or.inl (Or.inr hi)
  · intro x hx hxB
    have hstrip (i : Bool) (hi : (x : P2) ∈ c i '' source) : False := by
      have hcenter := (original_strip_double_trace c hcS hdis hτ h0 h1 hfull i).subset
        ⟨hi, hx⟩
      exact disjoint_left.mp (disjoint_center_far_images (c i) (hci i) (sign i))
        hcenter ((hcontact i).subset ⟨x.property, hi⟩)
    rcases hxB with (hxB | hxB) | hxB
    · exact hstrip false hxB
    · exact hstrip true hxB
    · exact disjoint_left.mp hKL x.property hxB
  · exact C.double_locus_eq_original_retained H old hdouble

end PoincareConjecture.M76.Dehn
