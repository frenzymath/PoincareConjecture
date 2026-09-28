import PoincareConjecture.Proofs.M76.Wall.ConnectedPLNeighborhood
import PoincareConjecture.Proofs.M76.Wall.WeakEndProtectedCore
import PoincareConjecture.Proofs.M76.Wall.WeakEndNoncompact












set_option autoImplicit false

open Set Geometry

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)






theorem exists_connected_weak_end_protected_PL_core
    {X ι : Type*} [TopologicalSpace X] [T2Space X]
    (e : ι → OpenPartialHomeomorph X V3) {R : Set X}
    (hR : PLDomain e R) (hconn : IsConnected R) (hB : IsCompact (frontier R))
    (hend : HasOneSimplyConnectedEnd R)
    {A : Set X} (hA : IsCompact A) (hAR : A ⊆ R) :
    ∃ C : Set X, IsCompact C ∧ IsConnected C ∧ PLDomain e C ∧ C ⊆ R ∧
      (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
        interior ((Subtype.val : R → X) ⁻¹' C) ∧
      ∃ D : Set R, IsCompact D ∧
        (Subtype.val : R → X) ⁻¹' C ⊆ interior D ∧ IsConnected Dᶜ ∧
        ∃ K S : Set X, IsCompact K ∧ IsConnected K ∧ C ⊆ K ∧ K ⊆ R ∧
          PLDomain e K ∧ S.Nonempty ∧ IsCompact S ∧ S ⊆ interior R ∧
          Disjoint (frontier R) S ∧ frontier K = frontier R ∪ S ∧
          (Subtype.val : R → X) ⁻¹' C ⊆
            interior ((Subtype.val : R → X) ⁻¹' K) ∧
          (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) ⊆
            interior ((Subtype.val : R → X) ⁻¹' K) ∧
          frontier ((Subtype.val : R → X) ⁻¹' K) =
            (Subtype.val : R → X) ⁻¹' S ∧
          Disjoint ((Subtype.val : R → X) '' D) S ∧
          ∀ (x : R) (p : Path x x),
            (∀ t, p t ∈ (Subtype.val : R → X) ⁻¹' S) →
            ∃ H : p.Homotopy (Path.refl x),
              ∀ z, H z ∉ (Subtype.val : R → X) ⁻¹' C := by
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hconn
  obtain ⟨C, G, hC, hCconn, _, hCR, hCPL, _, _, _, _, hCprotect, _⟩ :=
    exists_connected_protected_PL_neighborhood e hR hconn hB hA hAR
  have hCrel : IsCompact ((Subtype.val : R → X) ⁻¹' C) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hC
      (by simpa only [Subtype.range_coe] using hCR)
  obtain ⟨D, hD, hCD, hDconn, P, F, hP, hCP, hPR, hPPL,
      hF, hFi, hBF, hfront, hprotect, hrel, hDF, hloops⟩ :=
    exists_weak_end_protected_PL_core e hR hB hend hC hCR hCrel
  obtain ⟨x, hxC⟩ := hCconn.nonempty
  have hxP : x ∈ P := hCP hxC
  let K := connectedComponentIn P x
  have hK : IsCompact K := Set.isCompact_connectedComponentIn_of_mem hP hxP
  have hKconn : IsConnected K := isConnected_connectedComponentIn_iff.mpr hxP
  have hKP : K ⊆ P := connectedComponentIn_subset P x
  have hCK : C ⊆ K := hCconn.isPreconnected.subset_connectedComponentIn hxC hCP
  have hBC : frontier R ⊆ C := by
    intro y hy
    have hyR := hR.closed.frontier_subset hy
    have hyC : (⟨y, hyR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' C :=
      interior_subset (hCprotect (show (⟨y, hyR⟩ : R) ∈
        (Subtype.val : R → X) ⁻¹' (A ∪ frontier R) from Or.inr hy))
    exact hyC
  let : LocallyPathConnectedSpace P := hPPL.locallyPathConnectedSpace
  have hKfront := Set.protected_frontiers_of_relative_open hPPL.closed hK.isClosed
    hKP (Set.isOpen_preimage_connectedComponentIn hxP) (hBC.trans hCK) hfront hrel
  have hKprotect : (Subtype.val : R → X) ⁻¹' C ⊆
      interior ((Subtype.val : R → X) ⁻¹' K) := by
    rw [hKfront.2.2]
    intro y hy
    exact ⟨hCK hy, hprotect (Or.inl hy)⟩
  have hKrel : IsCompact ((Subtype.val : R → X) ⁻¹' K) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKP.trans hPR)
  have hKne : ((Subtype.val : R → X) ⁻¹' K).Nonempty :=
    ⟨⟨x, hCR hxC⟩, hCK hxC⟩
  have hFne : (F ∩ K).Nonempty := by
    have h := hend.frontier_nonempty_of_isCompact hKrel hKne
    rw [hKfront.2.1] at h
    obtain ⟨y, hy⟩ := h
    exact ⟨y, hy⟩
  refine ⟨C, hC, hCconn, hCPL, hCR, hCprotect, D, hD, hCD, hDconn,
    K, F ∩ K, hK, hKconn, hCK, hKP.trans hPR,
    hPPL.connectedComponentIn hP hxP, hFne, hF.inter_right hK.isClosed,
    inter_subset_left.trans hFi, hBF.mono_right inter_subset_left,
    hKfront.1, hKprotect, ?_, hKfront.2.1, hDF.mono_right inter_subset_left, ?_⟩
  · intro y hy
    exact hKprotect (interior_subset (hCprotect hy))
  · intro y p hp
    exact hloops y p (fun t => (hp t).1)

end PoincareConjecture.M76
