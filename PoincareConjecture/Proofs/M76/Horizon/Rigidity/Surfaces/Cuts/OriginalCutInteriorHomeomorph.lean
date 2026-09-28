import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.OriginalCutInteriorEmbedding
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Surfaces.Cuts.PrimalCutBoundaryArcs
import Mathlib.Topology.LocalAtTarget

set_option autoImplicit false

open Set Geometry Classical Topology
open PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  {K : SimplicialComplex ℝ E} [Fintype K.faces] [Fintype K.vertices]
  [Fintype K.barycentricSubdivision.faces]
  {P : SimpleGraph K.vertices}
  {D : SimpleGraph (PreAbstractSimplicialComplex.ModTwoCochains.Triangle
    K.vertexAbstractComplex.toPreAbstractSimplicialComplex)}
  {hD : D ≤ complementaryTriangleGraph K.vertexAbstractComplex.toPreAbstractSimplicialComplex P}
  {hcofaces : ∀ e ∈ K.faces, e.card = 2 →
    {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ e ⊆ t}.ncard = 2}
  {hP : P ≤ K.vertexAbstractComplex.edgeGraph}
  [Fintype (ResidualComplementaryEdge K P D)]
  {labels : ResidualComplementaryEdge K P D ≃ Fin 2}
  (A : OriginalPrimalCutDiskData K P D hD hcofaces hP labels)
  (hbound : ∀ s ∈ K.faces, s.card ≤ 3)

include hbound

theorem cutGraph_isCompact : IsCompact A.cutGraph := by
  have hr : IsCompact A.rim := by
    rw [← A.longBoundaryArcs_cover]
    exact isCompact_iUnion (fun i ↦ (A.longBoundaryArc_isFinitePLInterval hbound i).isCompact)
  rw [← A.sourceMap_rim_image]
  exact hr.image_of_continuousOn (A.sourceMapPL.continuousOn.mono A.disk.1)

theorem exists_interior_homeomorph :
    ∃ H : ↥(A.carrier \ A.rim) ≃ₜ ↥(K.space \ A.cutGraph),
      ∀ p, (H p : E) = (A.sourceMap) p := by
  let f : A.carrier → K.space := fun p ↦
    ⟨(A.sourceMap) p, A.sourceMap_image.subset (mem_image_of_mem _ p.property)⟩
  have hf : Continuous f := by
    change Continuous (fun p : A.carrier ↦ (⟨p.val.1.1, _⟩ : K.space))
    fun_prop
  let c : Set K.space := {x | (x : E) ∉ A.cutGraph}
  let _ : CompactSpace A.carrier := isCompact_iff_compactSpace.mp A.disk.isCompact
  have hclosed := hf.isClosedMap.restrictPreimage c
  have hg : Function.Bijective (c.restrictPreimage f) := by
    constructor
    · intro p q heq
      apply Subtype.ext
      apply Subtype.ext
      have he : (A.sourceMap) p.val = (A.sourceMap) q.val :=
        congrArg (fun z : c ↦ (z.val : E)) heq
      rcases A.sourceMap_fiber_eq_or_rim hbound p.val.property q.val.property he with h | h
      · exact h
      · exact (p.property (A.sourceMap_rim_image.subset (mem_image_of_mem _ h.1))).elim
    · intro x
      obtain ⟨p, hp, hpx⟩ := A.sourceMap_image.symm.subset x.val.property
      refine ⟨⟨⟨p, hp⟩, ?_⟩, ?_⟩
      · change (A.sourceMap) p ∉ A.cutGraph
        change p.1.1 ∉ A.cutGraph
        change p.1.1 = (x.val : E) at hpx
        rw [hpx]
        exact x.property
      · exact Subtype.ext (Subtype.ext hpx)
  let H := (Equiv.ofBijective (c.restrictPreimage f) hg).toHomeomorphOfContinuousClosed
    hf.restrictPreimage hclosed
  let J : ↥(A.carrier \ A.rim) ≃ₜ ↥(f ⁻¹' c) :=
    { toFun := fun p ↦ ⟨⟨p, p.property.1⟩, by
        change (A.sourceMap) p ∉ A.cutGraph
        exact fun h ↦ p.property.2 (A.mem_rim_of_sourceMap_mem_cutGraph hbound p.property.1 h)⟩
      invFun := fun p ↦ ⟨p.val, p.val.property, by
        intro h
        exact p.property (A.sourceMap_rim_image.subset (mem_image_of_mem _ h))⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let T : c ≃ₜ ↥(K.space \ A.cutGraph) :=
    { toFun := fun x ↦ ⟨x.val, x.val.property, x.property⟩
      invFun := fun x ↦ ⟨⟨x, x.property.1⟩, x.property.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  exact ⟨J.trans (H.trans T), fun _ ↦ rfl⟩

theorem sourceMap_interior_isOpenEmbedding :
    IsOpenEmbedding (fun p : ↥(A.carrier \ A.rim) ↦
      (⟨(A.sourceMap) p,
        A.sourceMap_image.subset (mem_image_of_mem _ p.property.1)⟩ : K.space)) := by
  obtain ⟨H, hH⟩ := A.exists_interior_homeomorph hbound
  have ho : IsOpen ((Subtype.val : K.space → E) ⁻¹' (K.space \ A.cutGraph)) := by
    have he : (Subtype.val : K.space → E) ⁻¹' (K.space \ A.cutGraph) =
        (Subtype.val : K.space → E) ⁻¹' A.cutGraphᶜ := by
      ext x
      exact and_iff_right x.property
    rw [he]
    exact (A.cutGraph_isCompact hbound).isClosed.isOpen_compl.preimage continuous_subtype_val
  have hi := Topology.IsOpenEmbedding.inclusion
    (sdiff_subset : K.space \ A.cutGraph ⊆ K.space) ho
  have he : (fun p : ↥(A.carrier \ A.rim) ↦
      (⟨(A.sourceMap) p,
        A.sourceMap_image.subset (mem_image_of_mem _ p.property.1)⟩ : K.space)) =
      Set.inclusion (sdiff_subset : K.space \ A.cutGraph ⊆ K.space) ∘ H := by
    funext p
    exact Subtype.ext (hH p).symm
  rw [he]
  exact hi.comp H.isOpenEmbedding

end PoincareConjecture.M76.OriginalTriangleCopies.OriginalPrimalCutDiskData
