import PoincareConjecture.Proofs.M76.Wall.PLDomainComponents
import PoincareConjecture.Proofs.M76.Wall.WeakEndNoncompact
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ClopenProtectedFrontier










set_option autoImplicit false

open Set

namespace PoincareConjecture.M76

theorem PLDomain.exists_connected_protected_compression_component
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {R C L F : Set X}
    (hL : PLDomain e L) (hLc : IsCompact L) (hLR : L ⊆ R)
    (hRconn : IsConnected R) (hend : HasOneSimplyConnectedEnd R)
    (hCconn : IsConnected C) (hCR : C ⊆ R) (hBC : frontier R ⊆ C)
    (hF : IsCompact F) (hFi : F ⊆ interior R)
    (hfront : frontier L = frontier R ∪ F)
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' L) = (Subtype.val : R → X) ⁻¹' F)
    (hprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' L)) :
    ∃ (x : X) (M : Set X), x ∈ C ∧ M = _root_.connectedComponentIn L x ∧
      IsCompact M ∧ IsConnected M ∧ PLDomain e M ∧
      C ⊆ M ∧ M ⊆ L ∧ M ⊆ R ∧
      (F ∩ M).Nonempty ∧ IsCompact (F ∩ M) ∧ F ∩ M ⊆ interior R ∧
      Disjoint (frontier R) (F ∩ M) ∧
      frontier M = frontier R ∪ (F ∩ M) ∧
      frontier ((Subtype.val : R → X) ⁻¹' M) = (Subtype.val : R → X) ⁻¹' (F ∩ M) ∧
      ((Subtype.val : R → X) ⁻¹' C ⊆ interior ((Subtype.val : R → X) ⁻¹' M)) ∧
      (Subtype.val : R → X) ⁻¹' frontier R ⊆
        interior ((Subtype.val : R → X) ⁻¹' M) := by
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRconn
  let : LocallyPathConnectedSpace L := hL.locallyPathConnectedSpace
  have hCL : C ⊆ L := by
    intro y hy
    have hh := hprotect (show (⟨y, hCR hy⟩ : R) ∈
      (Subtype.val : R → X) ⁻¹' C from hy)
    exact (interior_subset hh : (⟨y, hCR hy⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' L)
  obtain ⟨x, hxC⟩ := hCconn.nonempty
  have hxL : x ∈ L := hCL hxC
  let M := _root_.connectedComponentIn L x
  have hMc : IsCompact M := Set.isCompact_connectedComponentIn_of_mem hLc hxL
  have hMconn : IsConnected M := isConnected_connectedComponentIn_iff.mpr hxL
  have hML : M ⊆ L := connectedComponentIn_subset L x
  have hMR : M ⊆ R := hML.trans hLR
  have hCM : C ⊆ M := hCconn.isPreconnected.subset_connectedComponentIn hxC hCL
  have hMfront := Set.protected_frontiers_of_relative_open hL.closed hMc.isClosed hML
    (Set.isOpen_preimage_connectedComponentIn hxL) (hBC.trans hCM) hfront hrel
  have hMprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' M) := by
    rw [hMfront.2.2]
    exact fun _ hy => ⟨hCM hy, hprotect hy⟩
  have hMrelcompact : IsCompact ((Subtype.val : R → X) ⁻¹' M) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hMc
      (by simpa only [Subtype.range_coe] using hMR)
  have hMrelne : ((Subtype.val : R → X) ⁻¹' M).Nonempty :=
    ⟨⟨x, hCR hxC⟩, hCM hxC⟩
  have hFne : (F ∩ M).Nonempty := by
    have hh := hend.frontier_nonempty_of_isCompact hMrelcompact hMrelne
    rw [hMfront.2.1] at hh
    obtain ⟨y, hy⟩ := hh
    exact ⟨y, hy⟩
  refine ⟨x, M, hxC, rfl, hMc, hMconn, hL.connectedComponentIn hLc hxL,
    hCM, hML, hMR, hFne, hF.inter_right hMc.isClosed,
    inter_subset_left.trans hFi, ?_, hMfront.1, hMfront.2.1, hMprotect, ?_⟩
  · exact disjoint_left.mpr (fun _ hb hf => hb.2 (hFi hf.1))
  · exact fun _ hb => hMprotect (hBC hb)

end PoincareConjecture.M76
