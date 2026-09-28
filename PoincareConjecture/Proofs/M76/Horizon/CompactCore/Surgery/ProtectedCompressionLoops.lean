import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.FrontierBlockLoopContractions
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Surgery.ProtectedBlockFrontier
import PoincareConjecture.Proofs.M76.Horizon.CompactCore.Topology.ProtectedLoopTransport











set_option autoImplicit false

open Set Metric Geometry

namespace PoincareConjecture.M76

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1
local notation "I" => Icc (-1 : ℝ) 1

theorem OriginalDiskProduct.compressed_frontier_subset_block
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {L F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) :
    (F \ P.openStrip) ∪ P.endDisks ⊆ F ∪ P.closedStrip := by
  rintro x (hx | ⟨⟨z, t⟩, ⟨hz, ht⟩, rfl⟩)
  · exact Or.inl hx.1
  · refine Or.inr ⟨(z, t), ⟨hz, ?_⟩, rfl⟩
    rcases ht with ht | ht
    · rw [ht]
      norm_num
    · rw [mem_singleton_iff.mp ht]
      norm_num

theorem OriginalDiskProduct.protected_compression_frontier_loops
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3} {L U R C F : Set X} {j : V2 → X}
    (P : OriginalDiskProduct e L j) (hF : IsCompact F)
    (hcut : U ∩ frontier L = F) (hUY : U ⊆ R \ C)
    (hsmall : MapsTo P.map (D ×ˢ I) U)
    (hlateral : IsOpen ((Subtype.val : frontier L → X) ⁻¹'
      (P.map '' (Q ×ˢ Ioo (-(3 / 4 : ℝ)) (3 / 4)))))
    (hloops : ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' F) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C) :
    ∀ (x : R) (p : Path x x),
      (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' ((F \ P.openStrip) ∪ P.endDisks)) →
      ∃ H : p.Homotopy (Path.refl x),
        ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C := by
  have hFY : F ⊆ R \ C := (hcut.symm.subset.trans inter_subset_left).trans hUY
  have hPY : MapsTo P.map (D ×ˢ I) (R \ C) := fun z hz => hUY (hsmall hz)
  have hZ := P.frontier_block_subset hFY hPY
  have hnew := P.compressed_frontier_subset_block (F := F)
  apply (protected_frontier_loop_contractions_iff (hnew.trans hZ)).mpr
  intro x p
  have hnull := P.frontier_block_loops_contract hF (P.protected_frontier_iff hcut hsmall)
    (isOpen_protected_frontier_preimage hcut hlateral) hFY hPY
    ((protected_frontier_loop_contractions_iff hFY).mp hloops)
    ((ContinuousMap.inclusion hnew) x) (p.map (ContinuousMap.inclusion hnew).continuous)
  exact hnull

end PoincareConjecture.M76
