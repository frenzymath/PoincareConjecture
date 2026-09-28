import PoincareConjecture.Proofs.M76.Mathlib.BoundedRegionIncidence












set_option autoImplicit false

open Set

namespace Set

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup X] [NormedSpace ℝ X]




theorem IsFinitePLBallPair.isConnected_sdiff_of_subset_boundary
    {C b q : Set X} (hC : IsFinitePLBallPair E C b) (hqb : q ⊆ b) :
    IsConnected (C \ q) := by
  apply hC.isConnected_sdiff.subset_closure
    (sdiff_subset_sdiff_right hqb)
  rw [hC.closure_sdiff]
  exact sdiff_subset




theorem IsFinitePLBallPair.closure_sdiff_of_subset_boundary
    {C b q : Set X} (hC : IsFinitePLBallPair E C b) (hqb : q ⊆ b) :
    closure (C \ q) = C := by
  apply Subset.antisymm (closure_minimal sdiff_subset hC.isCompact.isClosed)
  calc
    C = closure (C \ b) := hC.closure_sdiff.symm
    _ ⊆ closure (C \ q) := closure_mono (sdiff_subset_sdiff_right hqb)






theorem IsFinitePLBallPair.boundary_collar_subset_relative_region
    {C b e q S : Set X} (hC : IsFinitePLBallPair E C (b ∪ e))
    (hb : IsFinitePLBallPair (ℝ × ℝ) b q) (hCS : C ⊆ S)
    {V : Set S} (hV : IsOpen V)
    (hfront : ∀ x : S, x ∈ frontier V → (x : X) ∈ C → (x : X) ∈ q)
    (hside : ∀ x : S, (x : X) ∈ b \ q → x ∈ V) :
    (Subtype.val : S → X) ⁻¹' (C \ q) ⊆ V ∧
      (Subtype.val : S → X) ⁻¹' C ⊆ closure V := by
  let D : Set S := (Subtype.val : S → X) ⁻¹' (C \ q)
  have hqb : q ⊆ b ∪ e := hb.1.trans subset_union_left
  have hconn := hC.isConnected_sdiff_of_subset_boundary hqb
  have himage : (Subtype.val : S → X) '' D = C \ q :=
    image_preimage_eq_of_subset (by simpa using (sdiff_subset.trans hCS : C \ q ⊆ S))
  have hpre : IsPreconnected D := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [himage]
    exact hconn.isPreconnected
  have hdis : Disjoint (frontier V) D := by
    apply disjoint_left.mpr
    intro x hxf hxD
    exact hxD.2 (hfront x hxf hxD.1)
  obtain ⟨x, hxb, hxq⟩ := hb.sdiff_nonempty
  have hxC : x ∈ C := hC.1 (Or.inl hxb)
  let y : S := ⟨x, hCS hxC⟩
  have hmeet : (D ∩ V).Nonempty := ⟨y, ⟨hxC, hxq⟩, hside y ⟨hxb, hxq⟩⟩
  have hsub : D ⊆ V := hpre.m76_subset_of_disjoint_frontier hV hdis hmeet
  have hclosure : closure D = (Subtype.val : S → X) ⁻¹' C := by
    rw [Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
      himage, hC.closure_sdiff_of_subset_boundary hqb]
  refine ⟨hsub, ?_⟩
  rw [← hclosure]
  exact closure_mono hsub

end Set
