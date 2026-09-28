import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.FiniteAttachmentRim











set_option autoImplicit false
open Set Geometry

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem preimage_closedFaceComplement_space_eq_closure_compl
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K) :
    (Subtype.val : K.space → E) ⁻¹' (K.closedFaceComplement N).space =
      closure (((Subtype.val : K.space → E) ⁻¹' N.space)ᶜ) := by
  rw [K.closedFaceComplement_space_eq_closure_sdiff N hK hNK,
    Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image]
  congr 2
  ext x
  constructor
  · rintro ⟨hxK, hxN⟩
    exact ⟨⟨x, hxK⟩, hxN, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.property, hy⟩



theorem closedFaceComplement_closedFaceComplement_eq_of_relative_regular_closed
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hreg : closure (interior ((Subtype.val : K.space → E) ⁻¹' N.space)) =
      (Subtype.val : K.space → E) ⁻¹' N.space) :
    K.closedFaceComplement (K.closedFaceComplement N) = N := by
  classical
  let C := K.closedFaceComplement N
  let T := K.closedFaceComplement C
  have hTK : T ≤ K := K.closedFaceComplement_le C
  have hpre : (Subtype.val : K.space → E) ⁻¹' T.space =
      (Subtype.val : K.space → E) ⁻¹' N.space := by
    rw [K.preimage_closedFaceComplement_space_eq_closure_compl C hK
      (K.closedFaceComplement_le N),
      K.preimage_closedFaceComplement_space_eq_closure_compl N hK hNK,
      ← interior_compl, compl_compl, hreg]
  have hspace : T.space = N.space := by
    ext x
    constructor
    · intro hx
      exact Set.ext_iff.mp hpre ⟨x, space_subset_of_le hTK hx⟩ |>.mp hx
    · intro hx
      exact Set.ext_iff.mp hpre ⟨x, space_subset_of_le hNK hx⟩ |>.mpr hx
  have hfaces : T.faces = N.faces := by
    ext s
    have htransfer (A B : SimplicialComplex ℝ E) (hAK : A ≤ K) (hBK : B ≤ K)
        (hAB : A.space = B.space) (hs : s ∈ A.faces) : s ∈ B.faces := by
      obtain ⟨x, hx⟩ := Set.Nonempty.intrinsicInterior (convex_convexHull ℝ (s : Set E))
        (Finset.coe_nonempty.mpr (A.nonempty_of_mem_faces hs)).convexHull
      exact K.face_mem_subcomplex_of_intrinsicInterior B hBK (hAK hs) hx
        (hAB.subset (A.convexHull_subset_space hs (intrinsicInterior_subset hx)))
    exact ⟨htransfer T N hTK hNK hspace, htransfer N T hNK hTK hspace.symm⟩
  exact le_antisymm hfaces.subset hfaces.symm.subset

theorem pure_of_relative_regular_closed
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hreg : closure (interior ((Subtype.val : K.space → E) ⁻¹' N.space)) =
      (Subtype.val : K.space → E) ⁻¹' N.space) :
    ∀ s ∈ N.faces, ∃ t ∈ N.faces, t.card = 3 ∧ s ⊆ t := by
  have ht := K.closedFaceComplement_pure (K.closedFaceComplement N) hpure
  rwa [K.closedFaceComplement_closedFaceComplement_eq_of_relative_regular_closed N hK hNK hreg]
    at ht

open Classical in
theorem edge_coface_count_of_relative_regular_closed
    (K N : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hNK : N ≤ K)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hreg : closure (interior ((Subtype.val : K.space → E) ⁻¹' N.space)) =
      (Subtype.val : K.space → E) ⁻¹' N.space)
    {s : Finset E} (hs : s ∈ N.faces) (hsc : s.card = 2) :
    {t : Finset E | t ∈ N.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard =
      if s ∈ (N ⊓ K.closedFaceComplement N).faces then 1 else 2 := by
  classical
  have hdouble := K.closedFaceComplement_closedFaceComplement_eq_of_relative_regular_closed
    N hK hNK hreg
  have h := K.closedFaceComplement_edge_coface_count (K.closedFaceComplement N) hK
    (K.closedFaceComplement_le N) hpure (K.closedFaceComplement_pure N hpure)
    hcofaces (s := s) (hdouble.symm ▸ hs) hsc
  simpa only [hdouble, show s ∈ (N ⊓ K.closedFaceComplement N).faces ↔
    s ∈ (K.closedFaceComplement N).faces from and_iff_right hs] using h

end Geometry.SimplicialComplex

namespace PoincareConjecture.M76

open Metric
local notation "V3" => (Fin 3 → ℝ)



theorem hamiltonAttachingBlock_relative_regular_closed
    (ι κ : Type*) [Fintype ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] :
    closure (interior ((Subtype.val : frontier (latticeHandleDomain ι κ L) →
        LatticeHandleAmbient ι κ L) ⁻¹' hamiltonAttachingBlock ι κ L (3 / 2))) =
      (Subtype.val : frontier (latticeHandleDomain ι κ L) →
        LatticeHandleAmbient ι κ L) ⁻¹' hamiltonAttachingBlock ι κ L (3 / 2) := by
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
  have hCreg : closure (interior C) = C := by
    change closure (interior ((univ : Set S) ×ˢ closedBall (0 : κ → ℝ) (3 / 2))) = _
    rw [interior_prod_eq, interior_univ,
      interior_closedBall _ (by norm_num : (3 / 2 : ℝ) ≠ 0),
      closure_prod_eq, closure_univ, closure_ball _ (by norm_num : (3 / 2 : ℝ) ≠ 0)]
  have hqreg : closure (interior (q '' C)) = q '' C := by
    apply Subset.antisymm (closure_minimal interior_subset
      ((hC.image hq.continuous).isClosed))
    calc
      q '' C = q '' closure (interior C) := congrArg (Set.image q) hCreg.symm
      _ ⊆ closure (q '' interior C) := image_closure_subset_closure_image hq.continuous
      _ ⊆ closure (interior (q '' C)) := closure_mono (hq.isOpenMap.image_interior_subset C)
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
  change closure (interior ((Subtype.val : frontier R → LatticeHandleAmbient ι κ L) ⁻¹'
    hamiltonAttachingBlock ι κ L (3 / 2))) = _
  rw [← hmark, ← H.image_interior, ← H.image_closure, hqreg]

theorem HamiltonMarkedProtectedBall.marked_patch_finite_regular_closed
    {ι κ α E : Type*} [Fintype ι] [Fintype κ]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L] [IsZLattice ℝ L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D)
    (he : PLDomain e (latticeHandleDomain ι κ L)) (hpos : 0 < Fintype.card ι)
    (A J : SimplicialComplex ℝ E)
    (F : LatticeHandleAmbient ι κ L → E) (hF : Continuous F)
    (hinj : InjOn F (latticeHandleDomain ι κ L))
    (hAs : A.space = F '' frontier (latticeHandleDomain ι κ L))
    (hJs : J.space = F '' hamiltonAttachingBlock ι κ L (3 / 2)) :
    closure (interior ((Subtype.val : A.space → E) ⁻¹' J.space)) =
      (Subtype.val : A.space → E) ⁻¹' J.space := by
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
  rw [← himage, ← H.image_interior, ← H.image_closure,
    hamiltonAttachingBlock_relative_regular_closed ι κ L]

end PoincareConjecture.M76
