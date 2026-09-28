import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.PlanarSurfaceCarrierInterior
import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionBallInterior

set_option autoImplicit false
open Set Geometry Topology
namespace PoincareConjecture.M76
local notation "P2" => (ℝ × ℝ)

theorem isOpen_relative_planar_disk_of_connected_interior_germs
    {K B A U W : Set P2} (hA : IsFinitePLBallPair P2 A (U ∪ W))
    (hAK : A ⊆ K) (hUB : U ⊆ B) (hW : IsClosed W)
    (hB : Disjoint B (interior K))
    (hlocal : ∀ x ∈ K, ∀ O : Set P2, IsOpen O → x ∈ O →
      ∃ V : Set P2, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧
        IsPreconnected (V ∩ (K \ B)) ∧ V ∩ K ⊆ closure (V ∩ (K \ B))) :
    IsOpen ((Subtype.val : K → P2) ⁻¹' (A \ W)) := by
  rw [isOpen_iff_forall_mem_open]
  intro x hx
  obtain ⟨V,hV,hxV,hVO,hconn,hdense⟩ := hlocal x x.property Wᶜ hW.isOpen_compl hx.2
  have hxcl : (x : P2) ∈ closure (interior A) :=
    (hA.closure_interior_of_finrank_eq rfl).symm ▸ hx.1
  obtain ⟨y,hyV,hyA⟩ := mem_closure_iff.mp hxcl V hV hxV
  have hycore : y ∈ V ∩ (K \ B) :=
    ⟨hyV,hAK (interior_subset hyA),fun hyB =>
      disjoint_left.mp hB hyB (interior_mono hAK hyA)⟩
  have hcover : V ∩ (K \ B) ⊆ interior A ∪ Aᶜ := by
    intro z hz
    by_cases hzA : z ∈ A
    · apply Or.inl
      apply (mem_interior_iff_notMem_frontier hzA).mpr
      intro hzF
      have hzrim := (hA.frontier_eq_of_finrank_eq rfl).subset hzF
      rcases hzrim with hzU | hzW
      · exact hz.2.2 (hUB hzU)
      · exact hVO hz.1 hzW
    · exact Or.inr hzA
  have hside : V ∩ (K \ B) ⊆ interior A := by
    rcases hconn.subset_or_subset isOpen_interior hA.isCompact.isClosed.isOpen_compl
        (disjoint_left.mpr fun _ hi hn => hn (interior_subset hi)) hcover with h | h
    · exact h
    · exact (h hycore (interior_subset hyA)).elim
  have hVA : V ∩ K ⊆ A := by
    intro z hz
    have h := closure_mono hside (hdense hz)
    rwa [hA.closure_interior_of_finrank_eq rfl] at h
  refine ⟨Subtype.val ⁻¹' V,?_,hV.preimage continuous_subtype_val,hxV⟩
  intro z hz
  exact ⟨hVA ⟨hz,z.property⟩,hVO hz⟩

theorem exists_closed_planar_disk_complement_of_relative_open
    {K A U W : Set P2} (hK : IsCompact K)
    (hA : IsFinitePLBallPair P2 A (U ∪ W)) (hAK : A ⊆ K)
    (hopen : IsOpen ((Subtype.val : K → P2) ⁻¹' (A \ W))) :
    ∃ B : Set P2, IsCompact B ∧ A ∪ B = K ∧ A ∩ B = W := by
  let B := K \ (A \ W)
  have hrel : IsClosed ((Subtype.val : K → P2) ⁻¹' B) := by
    have heq : ((Subtype.val : K → P2) ⁻¹' B) =
        ((Subtype.val : K → P2) ⁻¹' (A \ W))ᶜ := by
      ext x
      simp only [B,mem_preimage,mem_sdiff,x.property,true_and,mem_compl_iff]
    rw [heq]
    exact hopen.isClosed_compl
  have hB : IsClosed B := by
    have hemb := hK.isClosed.isClosedEmbedding_subtypeVal
    have himage : Subtype.val '' ((Subtype.val : K → P2) ⁻¹' B) = B := by
      exact image_preimage_eq_of_subset (fun _ hx => ⟨⟨_,hx.1⟩,rfl⟩)
    rw [←himage]
    exact hemb.isClosedMap _ hrel
  refine ⟨B,hK.of_isClosed_subset hB sdiff_subset,?_,?_⟩
  · ext x
    constructor
    · exact fun h => h.elim (fun hx => hAK hx) And.left
    · intro hx
      by_cases hxA : x ∈ A
      · exact Or.inl hxA
      · exact Or.inr ⟨hx,fun h => hxA h.1⟩
  · ext x
    constructor
    · intro h
      by_contra hxW
      exact h.2.2 ⟨h.1,hxW⟩
    · intro hx
      have hxA := hA.1 (Or.inr hx)
      exact ⟨hxA,hAK hxA,fun h => h.2 hx⟩

end PoincareConjecture.M76
