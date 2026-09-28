import PoincareConjecture.Proofs.M76.Wall.OriginalEndComponentFilling
import PoincareConjecture.Proofs.M76.Wall.ProtectedFrontierBicollar
import PoincareConjecture.Proofs.M76.Wall.BicollarDomainRestriction
import PoincareConjecture.Proofs.M76.Wall.FiniteBicollarSelection
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteClosedPieces
import PoincareConjecture.Proofs.M76.Wall.FilledPLDomain

set_option autoImplicit false

open Set BrownCollar

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_finite_frontier_filling
    {X ι κ : Type*} [TopologicalSpace X] [T2Space X] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {R K : Set X}
    (hR : PLDomain e R) (hRconn : IsConnected R)
    (hend : HasOneSimplyConnectedEnd R)
    (hK : PLDomain e K) (hKc : IsCompact K) (hKconn : IsConnected K) (hKR : K ⊆ R)
    (S : κ → Set X) (hSc : ∀ i, IsCompact (S i))
    (hSconn : ∀ i, IsConnected (S i))
    (hdisjoint : Pairwise fun i j => Disjoint (S i) (S j))
    (hSint : ∀ i, S i ⊆ interior R)
    (hfront : frontier K = frontier R ∪ ⋃ i, S i)
    (hrel : frontier ((Subtype.val : R → X) ⁻¹' K) =
      (Subtype.val : R → X) ⁻¹' (⋃ i, S i))
    (hprotect : (Subtype.val : R → X) ⁻¹' frontier R ⊆
      interior ((Subtype.val : R → X) ⁻¹' K)) :
    ∃ (L : Set X) (J : Finset κ), J.Nonempty ∧
      IsCompact L ∧ IsConnected L ∧ K ⊆ L ∧ L ⊆ R ∧ PLDomain e L ∧
      frontier L = frontier R ∪ (⋃ i ∈ J, S i) ∧
      frontier ((Subtype.val : R → X) ⁻¹' L) =
        (Subtype.val : R → X) ⁻¹' (⋃ i ∈ J, S i) ∧
      IsConnected (((Subtype.val : R → X) ⁻¹' L)ᶜ) ∧
      ∀ P : Set X, (Subtype.val : R → X) ⁻¹' P ⊆
          interior ((Subtype.val : R → X) ⁻¹' K) →
        (Subtype.val : R → X) ⁻¹' P ⊆
          interior ((Subtype.val : R → X) ⁻¹' L) := by
  classical
  let : ConnectedSpace R := isConnected_iff_connectedSpace.mp hRconn
  let F : Set X := ⋃ i, S i
  let k : Set R := (Subtype.val : R → X) ⁻¹' K
  let SR : κ → Set R := fun i => (Subtype.val : R → X) ⁻¹' S i
  obtain ⟨L, x, hx, hLc, hLconn, hKL, hLR, hUopen, hUconn, hpre, hbound, hmono⟩ :=
    exists_original_compact_connected_filling hR hRconn hend hKc hKconn hKR
  let U := connectedComponentIn kᶜ x
  have hUF : frontier U ⊆ (Subtype.val : R → X) ⁻¹' F := by
    rw [hpre, frontier_compl] at hbound
    exact hbound.trans hrel.subset
  have hUne : (frontier U).Nonempty := by
    apply nonempty_frontier_iff.mpr
    refine ⟨⟨x, mem_connectedComponentIn hx⟩, ?_⟩
    intro hUU
    obtain ⟨y, hy⟩ := hKconn.nonempty
    have hyU : (⟨y, hKR hy⟩ : R) ∈ U := by
      rw [hUU]
      trivial
    exact connectedComponentIn_subset kᶜ x hyU hy
  have hFne : F.Nonempty := by
    obtain ⟨y, hy⟩ := hUne
    exact ⟨y.val, hUF hy⟩
  have hFint : F ⊆ interior R := iUnion_subset hSint
  have hcut : interior R ∩ frontier K = F := by
    rw [hfront]
    ext y
    constructor
    · rintro ⟨hyR, hyB | hyF⟩
      · exact False.elim (hyB.2 hyR)
      · exact hyF
    · intro hy
      exact ⟨hFint hy, Or.inr hy⟩
  obtain ⟨C, hC, hFC, hCRint, H, hbase, hside, _⟩ :=
    hK.exists_protected_frontier_bicollar isOpen_interior
      (isCompact_iUnion hSc) hFne hcut
  obtain ⟨G, _, hGb, hGs⟩ := exists_bicollar_in_domain H
    (hCRint.trans interior_subset) hbase hside
  have hSRconn (i : κ) : IsConnected (SR i) := by
    have hrange : S i ⊆ range (Subtype.val : R → X) := by
      simpa only [Subtype.range_coe] using (hSint i).trans interior_subset
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨y, hy⟩ := (hSconn i).nonempty
      exact ⟨⟨y, interior_subset (hSint i hy)⟩, hy⟩
    · change IsPreconnected ((Subtype.val : R → X) ''
        ((Subtype.val : R → X) ⁻¹' S i))
      rw [image_preimage_eq_of_subset hrange]
      exact (hSconn i).isPreconnected
  have hSRclosed (i : κ) : IsClosed (SR i) :=
    (hSc i).isClosed.preimage continuous_subtype_val
  have hSRdisjoint : Pairwise fun i j => Disjoint (SR i) (SR j) :=
    fun _ _ hij => (hdisjoint hij).preimage Subtype.val
  have hfamily : (Subtype.val : R → X) ⁻¹' F = ⋃ i, SR i := by
    simp only [F, SR, preimage_iUnion]
  have hopen (i : κ) :
      IsOpen ((Subtype.val : ((Subtype.val : R → X) ⁻¹' F) → R) ⁻¹' SR i) := by
    rw [hfamily]
    exact Set.isOpen_preimage_iUnion_piece SR hSRclosed hSRdisjoint i
  obtain ⟨J, hJne, hJfront, hJlocal⟩ :=
    exists_finite_bicollar_frontier_selection G (hC.preimage continuous_subtype_val)
      hGb hGs SR hfamily hSRconn hopen hx hUF hUne
  have hLrel : frontier ((Subtype.val : R → X) ⁻¹' L) =
      (Subtype.val : R → X) ⁻¹' (⋃ i ∈ J, S i) := by
    rw [hpre, frontier_compl]
    simpa only [SR, preimage_iUnion] using hJfront
  have hretF : (⋃ i ∈ J, S i) ⊆ F := by
    intro y hy
    obtain ⟨i, _, hyi⟩ := mem_iUnion₂.mp hy
    exact mem_iUnion.mpr ⟨i, hyi⟩
  have hretK : (⋃ i ∈ J, S i) ⊆ frontier K := by
    rw [hfront]
    exact hretF.trans subset_union_right
  have hlocal : ∀ y ∈ (⋃ i ∈ J, S i), ∃ V : Set X, IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, z ∈ L ↔ z ∈ K := by
    intro y hy
    obtain ⟨i, hi, hyi⟩ := mem_iUnion₂.mp hy
    obtain ⟨V0, hV0, hSV, _, hsame⟩ := hJlocal i hi
    obtain ⟨W, hW, hWV⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp hV0
    have hyR : y ∈ R := interior_subset (hSint i hyi)
    have hyW : y ∈ W := by
      change (⟨y, hyR⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' W
      rw [hWV]
      exact hSV hyi
    refine ⟨W ∩ C, hW.inter hC, ⟨hyW, hFC (mem_iUnion.mpr ⟨i, hyi⟩)⟩, ?_⟩
    intro z hz
    have hzR : z ∈ R := interior_subset (hCRint hz.2)
    have hzV : (⟨z, hzR⟩ : R) ∈ V0 := by
      rw [← hWV]
      exact hz.1
    exact (Set.ext_iff.mp hpre (⟨z, hzR⟩ : R)).trans (hsame _ hzV)
  obtain ⟨hLPL, hLfront⟩ := hR.of_protected_local_agreement hK hLc.isClosed hLR
    (hretF.trans hFint) hretK (hmono (frontier R) hprotect) hLrel hlocal
  refine ⟨L, J, hJne, hLc, hLconn, hKL, hLR, hLPL, hLfront, hLrel, ?_, hmono⟩
  rw [hpre, compl_compl]
  exact hUconn

end PoincareConjecture.M76
