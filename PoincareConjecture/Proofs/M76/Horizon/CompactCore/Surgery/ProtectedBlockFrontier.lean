import PoincareConjecture.Proofs.M76.Rigidity.OriginalProductCut










set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.protected_frontier_iff
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {K U F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e K j) (hcut : U ∩ frontier K = F)
    (hsmall : MapsTo P.map (D ×ˢ I) U) :
    ∀ z ∈ D ×ˢ I, P.map z ∈ F ↔ z.1 ∈ Q := by
  intro z hz
  rw [← hcut, mem_inter_iff, and_iff_right (hsmall hz)]
  exact P.proper z hz

theorem isOpen_protected_frontier_preimage
    {X : Type*} [TopologicalSpace X] {K U F W : Set X}
    (hcut : U ∩ frontier K = F)
    (hW : IsOpen ((Subtype.val : frontier K → X) ⁻¹' W)) :
    IsOpen ((Subtype.val : F → X) ⁻¹' W) := by
  exact hW.preimage (continuous_inclusion (hcut.symm.subset.trans inter_subset_right))

theorem protected_local_exterior_frontier
    {X : Type*} [TopologicalSpace X] {K H L Y F : Set X}
    (hcut : Y ∩ frontier K = F) (hFH : F ⊆ interior H)
    (hfront : frontier L = frontier K ∪ (frontier H ∩ (interior K)ᶜ)) :
    (interior H ∩ Y) ∩ frontier L = F := by
  rw [hfront]
  apply Subset.antisymm
  · rintro x ⟨⟨hxH, hxY⟩, hxK | hxH'⟩
    · exact hcut.subset ⟨hxY, hxK⟩
    · exact (hxH'.1.2 hxH).elim
  · intro x hx
    exact ⟨⟨hFH hx, (hcut.superset hx).1⟩, Or.inl (hcut.superset hx).2⟩

end PoincareConjecture.M76
