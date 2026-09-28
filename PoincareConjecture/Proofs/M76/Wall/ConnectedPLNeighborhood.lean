import PoincareConjecture.Proofs.M76.Wall.Mathlib.CompactConnectedCarrier
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenProtectedFrontier
import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents
import PoincareConjecture.Proofs.M76.Wall.ProtectedPLNeighborhood











set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





theorem exists_connected_protected_PL_neighborhood
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (hR : PLDomain e R) (hconn : IsConnected R) (hB : IsCompact (frontier R))
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ C S : Set X, IsCompact C ∧ IsConnected C ∧ A ⊆ C ∧ C ⊆ R ∧ PLDomain e C ∧
      IsCompact S ∧ S ⊆ interior R ∧ Disjoint (frontier R) S ∧
      frontier C = frontier R ∪ S ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' C) ∧
      frontier ((Subtype.val : R → X) ⁻¹' C) = (Subtype.val : R → X) ⁻¹' S := by
  let : LocallyPathConnectedSpace R := hR.locallyPathConnectedSpace
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hconn
  let : PathConnectedSpace R := PathConnectedSpace.of_locallyPathConnectedSpace
  have hpath : IsPathConnected R := isPathConnected_iff_pathConnectedSpace.mpr inferInstance
  obtain ⟨x, hxR⟩ := hconn.nonempty
  have hAXR : A ∪ {x} ⊆ R := union_subset hAR (singleton_subset_iff.mpr hxR)
  obtain ⟨P0, S0, hP0, hAP0, hP0R, hP0PL, _, _, _, _, hprotect0, _⟩ :=
    exists_protected_PL_neighborhood e hR hB (hA.union isCompact_singleton) hAXR
  have hxP0 : x ∈ P0 := hAP0 (Or.inr (mem_singleton x))
  have hBP0 : frontier R ⊆ P0 := by
    intro y hy
    have hyR := hR.closed.frontier_subset hy
    have hyP0 : (⟨y, hyR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' P0 :=
      interior_subset (hprotect0 (show (⟨y, hyR⟩ : R) ∈
        (Subtype.val : R → X) ⁻¹' ((A ∪ {x}) ∪ frontier R) from Or.inr hy))
    exact hyP0
  let : LocallyPathConnectedSpace P0 := hP0PL.locallyPathConnectedSpace
  obtain ⟨T, hT, hTconn, hP0T, hTR⟩ :=
    Set.exists_compact_connected_carrier hP0 ⟨x, hxP0⟩ hP0R hpath
  have hxT : x ∈ T := hP0T hxP0
  have hAT : A ⊆ T := fun _ hy => hP0T (hAP0 (Or.inl hy))
  have hBT : frontier R ⊆ T := hBP0.trans hP0T
  obtain ⟨P, S, hP, hTP, hPR, hPPL, hS, hSi, hBS, hfront, hprotect, hrel⟩ :=
    exists_protected_PL_neighborhood e hR hB hT hTR
  have hxP : x ∈ P := hTP hxT
  let C := connectedComponentIn P x
  have hC : IsCompact C := Set.isCompact_connectedComponentIn_of_mem hP hxP
  have hCconn : IsConnected C := isConnected_connectedComponentIn_iff.mpr hxP
  have hCP : C ⊆ P := connectedComponentIn_subset P x
  have hTC : T ⊆ C := hTconn.isPreconnected.subset_connectedComponentIn hxT hTP
  let : LocallyPathConnectedSpace P := hPPL.locallyPathConnectedSpace
  have hopen : IsOpen ((Subtype.val : P → X) ⁻¹' C) :=
    Set.isOpen_preimage_connectedComponentIn hxP
  have hCfront := Set.protected_frontiers_of_relative_open hPPL.closed hC.isClosed
    hCP hopen (hBT.trans hTC) hfront hrel
  refine ⟨C, S ∩ C, hC, hCconn, hAT.trans hTC, hCP.trans hPR,
    hPPL.connectedComponentIn hP hxP, hS.inter_right hC.isClosed,
    inter_subset_left.trans hSi, hBS.mono_right inter_subset_left,
    hCfront.1, ?_, hCfront.2.1⟩
  rw [hCfront.2.2]
  intro y hy
  have hyT : (y : X) ∈ T := hy.elim (fun h => hAT h) (fun h => hBT h)
  exact ⟨hTC hyT, hprotect (Or.inl hyT)⟩

end PoincareConjecture.M76
