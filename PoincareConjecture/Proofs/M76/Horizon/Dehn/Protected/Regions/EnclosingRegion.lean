import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.ProductRegion
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Protected.Regions.Projection

set_option autoImplicit false
open Set Metric

namespace PoincareConjecture.M76.Dehn

theorem nonempty_enclosing_region_of_source_side
    {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ]
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L] {α : Type*}
    (e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) (Fin 3 → ℝ))
    {h : OpenPartialHomeomorph ((ι → ℝ) × (κ → ℝ)) (Fin 3 → ℝ)}
    (retained : HamiltonRetainedBlockChart ι κ L e h)
    {U K : Set ((ι → ℝ) × (κ → ℝ))}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hK : IsClosed K)
    (hinside : K ⊆ (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 2) \
      (closedBall (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) 1))
    (houter : K ⊆ closedBall (0 : ι → ℝ) 1 ×ˢ ball (0 : κ → ℝ) 2)
    (htraceK : K ∩ (sphere (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ))) ⊆
      sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2))
    (hfront : frontier U = K ∪
      (sphere (0 : ι → ℝ) 1 ×ˢ closedBall (0 : κ → ℝ) (3 / 2)))
    (hfrontClosure : frontier (closure U) = frontier U)
    (s : ChartwisePLSphere e ((hamiltonMarkedProjection ι κ L '' K) ∪
      hamiltonAttachingBlock ι κ L (3 / 2))) :
    Nonempty (HamiltonDehnEnclosingRegion ι κ L e
      (hamiltonMarkedProjection ι κ L '' K)) := by
  let pi := hamiltonMarkedProjection ι κ L
  obtain ⟨hbounds, hstrict, hcore, hrelative, htrace⟩ :=
    protected_product_region_bounds hU hbounded hK hinside houter htraceK hfront
  have hcompact : IsCompact (closure U) := hbounded.isCompact_closure
  have hwindow : closure U ⊆ (univ : Set (ι → ℝ)) ×ˢ ball (0 : κ → ℝ) 2 :=
    fun x hx ↦ ⟨mem_univ _, (hstrict hx).2⟩
  have hfrontImage : frontier (pi '' closure U) =
      (pi '' K) ∪ hamiltonAttachingBlock ι κ L (3 / 2) := by
    rw [retained.projection_frontier hcompact hwindow, hfrontClosure, hfront, image_union]
    rfl
  refine ⟨{
    region := pi '' closure U
    compact := hcompact.image continuous_hamiltonMarkedProjection
    core_subset := image_mono hcore
    subset_outer := image_mono hbounds
    subset_outer_open := image_mono hstrict
    core_relative_interior := ?_
    frontier_eq := hfrontImage
    old_boundary_eq := ?_
    sphere := hfrontImage.symm ▸ s
  }⟩
  · intro q hq
    obtain ⟨x, hx, heq⟩ := hq
    let xr : closedBall (0 : ι → ℝ) 1 ×ˢ (univ : Set (κ → ℝ)) :=
      ⟨x, hx.1, mem_univ _⟩
    have hxr : relativeMarkedProjection (L := L) xr = q := Subtype.ext heq
    rw [← hxr]
    exact (retained.projection_mem_relative_interior_iff hwindow xr
      ⟨mem_univ _, closedBall_subset_ball (by norm_num : (1 : ℝ) < 2) hx.2⟩).mpr
        (hrelative hx)
  · rw [hamiltonMarkedProjection_image_inter_frontier]
    exact congrArg (fun A ↦ pi '' A) htrace

end PoincareConjecture.M76.Dehn
