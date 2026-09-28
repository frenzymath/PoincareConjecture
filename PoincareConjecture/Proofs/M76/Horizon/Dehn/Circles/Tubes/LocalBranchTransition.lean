import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalBranchInverses

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D2" => closedBall (0 : V2) 1

variable {X ι : Type*} [TopologicalSpace X]
  {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X} {x y : V2}



theorem RawCrossingChart.connected_lift_in_one_branch
    (C : RawCrossingChart e f R x y) {A : Set V2}
    (hA : IsPreconnected A) (hAD : A ⊆ D2) (hAC : MapsTo f A C.chart.source) :
    A ⊆ C.left ∨ A ⊆ C.right := by
  have himage : (Subtype.val : D2 → V2) '' (Subtype.val ⁻¹' A) = A := by
    ext z
    exact ⟨fun ⟨u, hu, heq⟩ => heq ▸ hu, fun hz => ⟨⟨z, hAD hz⟩, hz, rfl⟩⟩
  have hconn : IsPreconnected ((Subtype.val : D2 → V2) ⁻¹' A) := by
    apply IsInducing.subtypeVal.isPreconnected_image.mp
    rwa [himage]
  have hcover : (Subtype.val : D2 → V2) ⁻¹' A ⊆
      Subtype.val ⁻¹' C.left ∪ Subtype.val ⁻¹' C.right := by
    intro z hz
    exact C.whole_preimage.subset ⟨z.property, hAC hz⟩
  rcases hconn.subset_or_subset C.left_open C.right_open
      (C.disjoint.preimage Subtype.val) hcover with hL | hR
  · exact Or.inl (fun z hz => hL (a := ⟨z, hAD hz⟩) hz)
  · exact Or.inr (fun z hz => hR (a := ⟨z, hAD hz⟩) hz)




theorem RawCrossingChart.exists_connected_lift_swap
    (C : RawCrossingChart e f R x y) {A B : Set V2}
    (hA : IsPreconnected A) (hB : IsPreconnected B)
    (hAD : A ⊆ D2) (hBD : B ⊆ D2)
    (hAC : MapsTo f A C.chart.source) (hBC : MapsTo f B C.chart.source)
    (ha : ∃ a ∈ A, ∃ b ∈ B, a ≠ b ∧ f a = f b) :
    ∃ swap : Bool,
      A ⊆ (if swap then C.right else C.left) ∧
      B ⊆ (if swap then C.left else C.right) := by
  obtain ⟨a, haA, b, hbB, hab, haf⟩ := ha
  have hnotL (hAL : A ⊆ C.left) (hBL : B ⊆ C.left) : False :=
    hab (congrArg Subtype.val (C.left_embedding.injective
      (a₁ := ⟨a, hAL haA⟩) (a₂ := ⟨b, hBL hbB⟩) haf))
  have hnotR (hAR : A ⊆ C.right) (hBR : B ⊆ C.right) : False :=
    hab (congrArg Subtype.val (C.right_embedding.injective
      (a₁ := ⟨a, hAR haA⟩) (a₂ := ⟨b, hBR hbB⟩) haf))
  rcases C.connected_lift_in_one_branch hA hAD hAC with hAL | hAR
  · exact ⟨false, hAL, (C.connected_lift_in_one_branch hB hBD hBC).resolve_left (hnotL hAL)⟩
  · exact ⟨true, hAR, (C.connected_lift_in_one_branch hB hBD hBC).resolve_right (hnotR hAR)⟩

end PoincareConjecture.M76.Dehn
