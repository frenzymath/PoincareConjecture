import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcGraphLift



set_option autoImplicit false
open Set
namespace PoincareConjecture.M76

theorem exists_region_pullback_of_compact_embedding
    {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
    [TopologicalSpace Y] [T2Space Y]
    (F : C(X,Y)) (hi : Function.Injective F)
    {U : Set Y} (hU : IsOpen U) (hsc : IsSimplyConnected U)
    (hsub : closure U ⊆ range F) :
    ∃ O : Set X, IsOpen O ∧ IsCompact (closure O) ∧ IsSimplyConnected O ∧
      F '' O = U ∧ F '' closure O = closure U ∧
      F '' frontier O = frontier U ∧ ∀ x, x ∈ O ↔ F x ∈ U := by
  let O := F ⁻¹' U
  have ho : IsOpen O := hU.preimage F.continuous
  have himage : F '' O = U := image_preimage_eq_of_subset (subset_closure.trans hsub)
  have hemb := F.continuous.isClosedEmbedding hi
  have hcl : F '' closure O = closure U := by
    rw [←hemb.closure_image_eq,himage]
  let f : O → U := fun x => ⟨F x,x.property⟩
  have hfs : Function.Surjective f := by
    intro y
    obtain ⟨x,hx,hxy⟩ := himage.symm.subset y.property
    exact ⟨⟨x,hx⟩,Subtype.ext hxy⟩
  have hfemb : Topology.IsEmbedding f := by
    exact (hemb.isEmbedding.comp (.subtypeVal)).codRestrict U (fun x => x.property)
  let H : O ≃ₜ U := hfemb.toHomeomorphOfSurjective hfs
  let : SimplyConnectedSpace U := hsc
  refine ⟨O,ho,isClosed_closure.isCompact,H.toHomotopyEquiv.simplyConnectedSpace,
    himage,hcl,?_,fun _ => Iff.rfl⟩
  rw [ho.frontier_eq,hU.frontier_eq,Set.image_sdiff hi,himage,hcl]

end PoincareConjecture.M76
