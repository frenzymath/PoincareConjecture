import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComplement
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Simplicial.ClosedSideSubcomplexes
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.SharedBoundaryConeUnion
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedAttachmentFiniteModel
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundedSphereRegion











set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]



theorem closedFaceComplement_space_eq_closure_sdiff
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K) :
    (K.closedFaceComplement N).space = closure (K.space \ N.space) := by
  apply Subset.antisymm
  · rw [K.closedFaceComplement_space N]
    intro x hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    apply (convex_convexHull ℝ (t : Set E)).subset_closure_intrinsicInterior.trans
      (closure_mono ?_) hxt
    intro y hy
    refine ⟨K.convexHull_subset_space ht.1 (intrinsicInterior_subset hy), ?_⟩
    intro hyN
    exact ht.2 (K.face_mem_subcomplex_of_intrinsicInterior N hNK ht.1 hy hyN)
  · apply closure_minimal ?_ ((K.closedFaceComplement N).isCompact_space_of_finite
      (K.closedFaceComplement_finite N hK)).isClosed
    intro x hx
    exact ((K.closedFaceComplement_space_cover N hNK).symm.subset hx.1).resolve_left hx.2



theorem inter_closedFaceComplement_space_eq_relative_frontier
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K) :
    (N ⊓ K.closedFaceComplement N).space =
      (Subtype.val : K.space → E) ''
        frontier ((Subtype.val : K.space → E) ⁻¹' N.space) := by
  have hNclosed := (N.isCompact_space_of_finite (hK.subset hNK)).isClosed
  rw [K.space_inf_eq_inter_of_le N (K.closedFaceComplement N) hNK
    (K.closedFaceComplement_le N),
    K.closedFaceComplement_space_eq_closure_sdiff N hK hNK,
    frontier_eq_closure_inter_closure,
    (hNclosed.preimage continuous_subtype_val).closure_eq,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  have hcomp : (Subtype.val : K.space → E) ''
      ((Subtype.val : K.space → E) ⁻¹' N.space)ᶜ = K.space \ N.space := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.property, hy⟩
    · rintro ⟨hxK, hxN⟩
      exact ⟨⟨x, hxK⟩, hxN, rfl⟩
  rw [hcomp]
  ext x
  constructor
  · rintro ⟨hxN, hxcl⟩
    exact ⟨⟨x, space_subset_of_le hNK hxN⟩, ⟨hxN, hxcl⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact hy

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Metric
local notation "V3" => (Fin 3 → ℝ)



theorem HamiltonMarkedProtectedBall.marked_rim_eq_relative_frontier
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    (Subtype.val : frontier (latticeHandleDomain ι κ L) → LatticeHandleAmbient ι κ L) ''
        frontier ((Subtype.val : frontier (latticeHandleDomain ι κ L) →
          LatticeHandleAmbient ι κ L) ⁻¹' hamiltonAttachingBlock ι κ L (3 / 2)) =
      hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)) := by
  let S := sphere (0 : ι → ℝ) 1
  let Y := (κ → ℝ) ⧸ L.toAddSubgroup
  let R := latticeHandleDomain ι κ L
  have hR : frontier R = S ×ˢ (univ : Set Y) := by
    change frontier (latticeHandleDomain ι κ L) = _
    rw [latticeHandleDomain, frontier_prod_univ_eq,
      frontier_closedBall _ (by norm_num : (1 : ℝ) ≠ 0)]
  let H : (S × Y) ≃ₜ frontier R :=
    { toEquiv :=
        { toFun := fun x => ⟨(x.1, x.2), hR.symm.subset ⟨x.1.property, mem_univ _⟩⟩
          invFun := fun x => (⟨x.val.1, (hR.subset x.property).1⟩, x.val.2)
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let q : (S × (κ → ℝ)) → (S × Y) := fun z => (z.1, QuotientAddGroup.mk z.2)
  have hq : IsLocalHomeomorph q :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.id_prod.isLocalHomeomorph
  let C : Set (S × (κ → ℝ)) := univ ×ˢ closedBall 0 (3 / 2)
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_sphere (0 : ι → ℝ) 1)
  have hC : IsCompact C := isCompact_univ.prod (isCompact_closedBall _ _)
  have hqi : InjOn q C := by
    intro x hx y hy hxy
    exact Prod.ext (congrArg (Prod.fst : S × Y → S) hxy)
      (b.quotient_injOn_attaching_disk hpos hx.2 hy.2 (congrArg Prod.snd hxy))
  have hfront := frontier_image_compact_of_localHomeomorph hq hC hqi
  have hfrontC : frontier C = (univ : Set S) ×ˢ sphere (0 : κ → ℝ) (3 / 2) := by
    change frontier ((univ : Set S) ×ˢ closedBall (0 : κ → ℝ) (3 / 2)) = _
    rw [frontier_univ_prod_eq, frontier_closedBall _ (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hmark : H '' (q '' C) =
      (Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹'
        hamiltonAttachingBlock ι κ L (3 / 2) := by
    ext x
    constructor
    · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
      exact ⟨(z.1, z.2), ⟨z.1.property, hz.2⟩, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨q (⟨z.1, hz.1⟩, z.2), ⟨(⟨z.1, hz.1⟩, z.2), ⟨mem_univ _, hz.2⟩, rfl⟩, ?_⟩
      exact Subtype.ext hzx
  change (Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ''
    frontier ((Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹'
      hamiltonAttachingBlock ι κ L (3 / 2)) = _
  rw [← hmark, ← H.image_frontier, hfront, hfrontC]
  ext x
  constructor
  · rintro ⟨_, ⟨_, ⟨z, hz, rfl⟩, rfl⟩, rfl⟩
    exact ⟨(z.1, z.2), ⟨z.1.property, hz.2⟩, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨H (q (⟨z.1, hz.1⟩, z.2)), ?_, rfl⟩
    exact ⟨q (⟨z.1, hz.1⟩, z.2),
      ⟨(⟨z.1, hz.1⟩, z.2), ⟨mem_univ _, hz.2⟩, rfl⟩, rfl⟩




theorem HamiltonMarkedProtectedBall.marked_rim_subcomplex_space
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L)) (hpos : 0 < Fintype.card ι)
    (A J : SimplicialComplex ℝ E) (hA : A.faces.Finite) (hJA : J ≤ A)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hinj : InjOn F (latticeHandleDomain ι κ L))
    (hAs : A.space = F '' frontier (latticeHandleDomain ι κ L))
    (hJs : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2)) :
    (J ⊓ A.closedFaceComplement J).space =
      F '' (hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2))) := by
  let R := latticeHandleDomain ι κ L
  let T := hamiltonAttachingBlock ι κ L (3 / 2)
  have hmark : D ∩ frontier R = T := by
    rcases b.position with ⟨hzero, _⟩ | ⟨_, _, _, _, _, hmark⟩
    · omega
    · exact hmark
  have hTR : T ⊆ frontier R := hmark.symm.subset.trans inter_subset_right
  let f : frontier R → A.space := fun x => ⟨F x, hAs.symm.subset ⟨x, x.property, rfl⟩⟩
  have : CompactSpace (frontier R) := isCompact_iff_compactSpace.mp
    ((isCompact_latticeHandleDomain ι κ L).of_isClosed_subset isClosed_frontier
      he.closed.frontier_subset)
  have hf : Continuous f := (hF.comp continuous_subtype_val).subtype_mk _
  have hfi : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    exact hinj (he.closed.frontier_subset x.property)
      (he.closed.frontier_subset y.property) (congrArg Subtype.val hxy)
  have hfs : Function.Surjective f := by
    rintro ⟨z, hz⟩
    obtain ⟨x, hx, rfl⟩ := hAs.subset hz
    exact ⟨⟨x, hx⟩, rfl⟩
  let H := (hf.isClosedEmbedding hfi).isEmbedding.toHomeomorphOfSurjective hfs
  have himage : H '' ((Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹' T) =
      (Subtype.val : A.space → E) ⁻¹' J.space := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hJs.symm.subset ⟨y, hy, rfl⟩
    · intro hx
      obtain ⟨y, hy, hyx⟩ := hJs.subset hx
      exact ⟨⟨y, hTR hy⟩, hy, Subtype.ext hyx⟩
  rw [A.inter_closedFaceComplement_space_eq_relative_frontier J hA hJA,
    ← himage, ← H.image_frontier, image_image]
  change (F ∘ (Subtype.val : frontier R → LatticeHandleAmbient ι κ L)) ''
    frontier ((Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹' T) = _
  exact (image_image F (Subtype.val : frontier R → LatticeHandleAmbient ι κ L)
    (frontier ((Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹' T))).symm.trans
      (congrArg (Set.image F) (b.marked_rim_eq_relative_frontier hpos))

end PoincareConjecture.M76
