import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Descent.Boundary.Nonspanning.Chain.Geometry
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Disks.Mathlib.MarkedIntervalDiskAttachment

set_option autoImplicit false
open Set Geometry TriangleDiskModel

namespace PoincareConjecture.M76.Dehn.NonspanningChainBoundaryData

local notation "P2" => (ℝ × ℝ)
local notation "TR" => convexHull ℝ (range rightTriangle)
local notation "TL" => convexHull ℝ (range leftTriangle)
local notation "T" => (TR ∪ TL : Set P2)

theorem exists_attachment_label {X : Type*} {S0 S1 : Set P2}
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL) (f0 f1 : P2 → X)
    (hagree : ∀ (x : S0) (y : S1), (n0 x : P2) = n1 y → f0 x = f1 y)
    (x0 : X) :
    ∃ g : P2 → X,
      (∀ x : S0, g (n0 x) = f0 x) ∧
      (∀ x : S1, g (n1 x) = f1 x) ∧
      ∀ U : Set X, T ∩ g ⁻¹' U =
        (fun x : S0 => (n0 x : P2)) '' {x : S0 | f0 x ∈ U} ∪
          (fun x : S1 => (n1 x : P2)) '' {x : S1 | f1 x ∈ U} := by
  classical
  let g : P2 → X := fun z => if h0 : z ∈ TR then f0 (n0.symm ⟨z, h0⟩)
    else if h1 : z ∈ TL then f1 (n1.symm ⟨z, h1⟩) else x0
  have hv0 (x : S0) : g (n0 x) = f0 x := by
    simp only [g, dif_pos (n0 x).property, n0.symm_apply_apply]
  have hv1 (x : S1) : g (n1 x) = f1 x := by
    by_cases hx : (n1 x : P2) ∈ TR
    · dsimp only [g]
      rw [dif_pos hx]
      exact hagree _ x (congrArg Subtype.val (n0.apply_symm_apply _))
    · simp only [g, dif_neg hx, dif_pos (n1 x).property, n1.symm_apply_apply]
  refine ⟨g, hv0, hv1, ?_⟩
  intro U
  ext z
  constructor
  · rintro ⟨hz | hz, hU⟩
    · let x := n0.symm ⟨z, hz⟩
      have hx : (n0 x : P2) = z := congrArg Subtype.val (n0.apply_symm_apply _)
      refine Or.inl ⟨x, ?_, hx⟩
      simpa only [← hx, mem_preimage, hv0, mem_ofPred_eq] using hU
    · let x := n1.symm ⟨z, hz⟩
      have hx : (n1 x : P2) = z := congrArg Subtype.val (n1.apply_symm_apply _)
      refine Or.inr ⟨x, ?_, hx⟩
      simpa only [← hx, mem_preimage, hv1, mem_ofPred_eq] using hU
  · rintro (⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩)
    · exact ⟨Or.inl (n0 x).property, by simpa only [mem_preimage, hv0, mem_ofPred_eq] using hx⟩
    · exact ⟨Or.inr (n1 x).property, by simpa only [mem_preimage, hv1, mem_ofPred_eq] using hx⟩

theorem complement_eq {E : Type*} {W B M P : Set E}
    (hunion : W ∪ B = M ∪ W) (hinter : W ∩ B = P) (hmark : W ∩ M = P) : B = M := by
  ext x
  have h0 := congrArg (fun U : Set E => x ∈ U) hunion
  have h1 := congrArg (fun U : Set E => x ∈ U) hinter
  have h2 := congrArg (fun U : Set E => x ∈ U) hmark
  simp only [mem_union, mem_inter_iff] at h0 h1 h2
  tauto

theorem marked_copy_image {X : Type*} {S V : Set P2} {f g : P2 → X} {Z : Set X}
    (j : S → P2) {a b : P2} (ha : a ∈ S) (hb : b ∈ S)
    (hmark : V ∩ f ⁻¹' Z = {a, b}) (hkeep : ∀ x : S, g (j x) = f x) :
    j '' (Subtype.val ⁻¹' V) ∩ g ⁻¹' Z = {j ⟨a, ha⟩, j ⟨b, hb⟩} := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hg⟩
    have hm : (x : P2) ∈ V ∩ f ⁻¹' Z := ⟨hx, by simpa only [mem_preimage, hkeep] using hg⟩
    rcases hmark.subset hm with hxa | hxb
    · exact Or.inl (congrArg j (Subtype.ext hxa))
    · exact Or.inr (congrArg j (Subtype.ext hxb))
  · rintro (rfl | rfl)
    · have hm := hmark.symm.subset (show a ∈ ({a, b} : Set P2) from Or.inl rfl)
      exact ⟨⟨⟨a, ha⟩, hm.1, rfl⟩, by simpa only [mem_preimage, hkeep] using hm.2⟩
    · have hm := hmark.symm.subset (show b ∈ ({a, b} : Set P2) from Or.inr rfl)
      exact ⟨⟨⟨b, hb⟩, hm.1, rfl⟩, by simpa only [mem_preimage, hkeep] using hm.2⟩

theorem remaining_eq_mark {X : Type*}
    {S0 Q0 W0 B0 P0 S1 Q1 W1 B1 P1 V1 V D : Set P2}
    {f0 f1 g : P2 → X} {Z : Set X} {a b : P2}
    (n0 : S0 ≃ₜ TR) (n1 : S1 ≃ₜ TL)
    (hW0S : W0 ⊆ S0) (hW1S : W1 ⊆ S1)
    (hWB0 : W0 ∪ B0 = Q0) (hWB1 : W1 ∪ B1 = Q1)
    (hi0 : W0 ∩ B0 = P0) (hi1 : W1 ∩ B1 = P1)
    (hQ0 : Q0 = (S0 ∩ f0 ⁻¹' Z) ∪ W0)
    (hQ1 : Q1 = ((S1 ∩ f1 ⁻¹' Z) ∪ V1) ∪ W1)
    (hmark0 : W0 ∩ f0 ⁻¹' Z = P0) (hmark1 : W1 ∩ f1 ⁻¹' Z = P1)
    (hdisj : W1 ∩ V1 = ∅)
    (hkeep1 : ∀ x : S1, g (n1 x) = f1 x)
    (hpre : T ∩ g ⁻¹' Z =
      (fun x : S0 => (n0 x : P2)) '' {x : S0 | f0 x ∈ Z} ∪
        (fun x : S1 => (n1 x : P2)) '' {x : S1 | f1 x ∈ Z})
    (hV : V = (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' V1))
    (ha : a ∈ S1) (hb : b ∈ S1) (hmarkV : V1 ∩ f1 ⁻¹' Z = {a, b})
    (hunion : V ∪ D =
      (fun x : S0 => (n0 x : P2)) '' (Subtype.val ⁻¹' B0) ∪
        (fun x : S1 => (n1 x : P2)) '' (Subtype.val ⁻¹' B1))
    (hinter : V ∩ D = {(n1 ⟨a, ha⟩ : P2), (n1 ⟨b, hb⟩ : P2)}) :
    D = T ∩ g ⁻¹' Z ∧
      V ∩ g ⁻¹' Z = {(n1 ⟨a, ha⟩ : P2), (n1 ⟨b, hb⟩ : P2)} := by
  have hrim := marked_attachment_rim_eq (fun x : S0 => (n0 x : P2))
    (fun x : S1 => (n1 x : P2)) hW0S hW1S hWB0 hWB1 hi0 hi1 hQ0 hQ1
      hmark0 hmark1 hdisj hpre
  rw [← hV] at hrim
  have hmark : V ∩ g ⁻¹' Z = {(n1 ⟨a, ha⟩ : P2), (n1 ⟨b, hb⟩ : P2)} := by
    rw [hV]
    exact marked_copy_image _ ha hb hmarkV hkeep1
  have hVT : V ⊆ T := by
    rw [hV]
    rintro z ⟨x, _, rfl⟩
    exact Or.inr (n1 x).property
  refine ⟨complement_eq (hunion.trans hrim) hinter ?_, hmark⟩
  rwa [← inter_assoc, inter_eq_left.mpr hVT]

end PoincareConjecture.M76.Dehn.NonspanningChainBoundaryData
