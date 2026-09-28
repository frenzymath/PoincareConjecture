import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Strips.DoubleTrace
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.TwoProperArcCuts



set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.Dehn

open PolygonalCrossingResolution

local notation "P2" => (ℝ × ℝ)
local notation "C3" => ((ℝ × ℝ) × ℝ)
local notation "Sq" => (Set.prod (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) : Set P2)

theorem spanning_strip_whole_component_retention
    {X J : Type*} {S : Set P2} {f : P2 → X} {τ : C3 → X}
    (c : Bool → P2 → P2) (hcS : ∀ i, MapsTo (c i) source S)
    (hci : ∀ i, InjOn (c i) source)
    (hdis : Disjoint (c false '' source) (c true '' source))
    (hτ : InjOn τ tube)
    (h0 : ∀ p ∈ source, f (c false p) = τ ((p.2, p.2), p.1))
    (h1 : ∀ p ∈ source, f (c true p) = τ ((p.2, -p.2), p.1))
    (hfull : S ∩ f ⁻¹' (τ '' tube) = c false '' source ∪ c true '' source)
    (E : Fin 2 → Set P2) (H : ∀ j, Sq ≃ₜ E j) (sign : Fin 2 → Bool → Bool)
    (hEdis : Disjoint (E 0) (E 1))
    (hcover : (c false '' source ∪ c true '' source) ∪ (E 0 ∪ E 1) = S)
    (hcontact : ∀ j i, E j ∩ (c i '' source) = c i '' arm (farArmParameter (sign j i)))
    (U : J → Set P2) (hU : ∀ k, U k ⊆ doubleLocusOn f S)
    (hconnected : ∀ k, IsConnected (U k))
    (hdisjoint : Pairwise (fun k l ↦ Disjoint (U k) (U l)))
    (selected : Bool → J) (hcenter : ∀ i, c i '' arm 0 = U (selected i)) :
    (∀ j k, U k ⊆ E j ∨ Disjoint (U k) (E j)) ∧
      ∀ j i, Disjoint (U (selected i)) (E j) ∧ ¬ U (selected i) ⊆ E j := by
  classical
  have hEclosed (j : Fin 2) : IsClosed (E j) := by
    let : CompactSpace Sq := isCompact_iff_compactSpace.mp (isCompact_Icc.prod isCompact_Icc)
    have hrange : range (fun z : Sq ↦ (H j z : P2)) = E j := by
      apply Subset.antisymm
      · rintro x ⟨z, rfl⟩
        exact (H j z).property
      · intro x hx
        exact ⟨(H j).symm ⟨x, hx⟩, congrArg Subtype.val ((H j).apply_symm_apply ⟨x, hx⟩)⟩
    rw [← hrange]
    exact (isCompact_range (continuous_subtype_val.comp (H j).continuous)).isClosed
  have hremoved (j : Fin 2) (i : Bool) : Disjoint (U (selected i)) (E j) := by
    rw [← hcenter i]
    refine disjoint_left.mpr ?_
    intro x hx hxE
    have hxS : x ∈ c i '' source := image_mono
      ((arm_zero_subset_halfSource false).trans (halfSource_subset_source false)) hx
    exact disjoint_left.mp (disjoint_center_far_images (c i) (hci i) (sign j i)) hx
      ((hcontact j i).subset ⟨hxE, hxS⟩)
  refine ⟨?_, ?_⟩
  · intro j k
    by_cases hsel : ∃ i, k = selected i
    · obtain ⟨i, rfl⟩ := hsel
      exact Or.inr (hremoved j i)
    have hstrip (i : Bool) : Disjoint (U k) (c i '' source) := by
      refine disjoint_left.mpr ?_
      intro x hx hxS
      have hxC := (original_strip_double_trace c hcS hdis hτ h0 h1 hfull i).subset
        ⟨hxS, hU k hx⟩
      rw [hcenter i] at hxC
      exact disjoint_left.mp (hdisjoint (fun h ↦ hsel ⟨i, h⟩)) hx hxC
    have hUE : U k ⊆ E 0 ∪ E 1 := by
      intro x hx
      rcases hcover.symm.subset (hU k hx).1 with (hx₀ | hx₁) | hxE
      · exact (disjoint_left.mp (hstrip false) hx hx₀).elim
      · exact (disjoint_left.mp (hstrip true) hx hx₁).elim
      · exact hxE
    rcases isPreconnected_subset_one_cut_piece (hconnected k).isPreconnected
      (hEclosed 0) (hEclosed 1) hUE hEdis.inter_eq (disjoint_empty _) with h | h
    · fin_cases j
      · exact Or.inl h
      · exact Or.inr (hEdis.mono_left h)
    · fin_cases j
      · exact Or.inr (hEdis.symm.mono_left h)
      · exact Or.inl h
  · intro j i
    refine ⟨hremoved j i, ?_⟩
    intro hsub
    have hx : c i (0, 0) ∈ U (selected i) := (hcenter i).subset
      ⟨(0, 0), ⟨by norm_num, rfl⟩, rfl⟩
    exact disjoint_left.mp (hremoved j i) hx (hsub hx)

end PoincareConjecture.M76.Dehn
