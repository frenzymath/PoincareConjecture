import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.MarkedBallCoverLift

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem mem_interior_of_relative_interior_at_interior
    {X : Type*} [TopologicalSpace X] {R D : Set X} (x : R)
    (hx : x ∈ interior ((Subtype.val : R → X) ⁻¹' D))
    (hxR : (x : X) ∈ interior R) : (x : X) ∈ interior D := by
  obtain ⟨U,hU,hpre⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior ((Subtype.val : R → X) ⁻¹' D)))
  have hxU : (x : X) ∈ U := by
    change x ∈ (Subtype.val : R → X) ⁻¹' U
    rw [hpre]
    exact hx
  have hsub : U ∩ interior R ⊆ D := by
    intro y hy
    have hyy : (⟨y,interior_subset hy.2⟩ : R) ∈
        interior ((Subtype.val : R → X) ⁻¹' D) := hpre ▸ hy.1
    exact (show (⟨y,interior_subset hy.2⟩ : R) ∈ (Subtype.val : R → X) ⁻¹' D from
      interior_subset hyy)
  exact interior_mono hsub ((hU.inter isOpen_interior).interior_eq.symm ▸ ⟨hxU,hxR⟩)

theorem HamiltonMarkedProtectedBall.core_disjoint_lateral
    {ι κ α : Type*} [Fintype ι] [Fintype κ]
    {L : Submodule ℤ (κ → ℝ)} [DiscreteTopology L]
    {e : α → OpenPartialHomeomorph (LatticeHandleAmbient ι κ L) V3}
    {D : Set (LatticeHandleAmbient ι κ L)}
    (b : HamiltonMarkedProtectedBall ι κ L e D) (hpos : 0 < Fintype.card ι) :
    Disjoint (hamiltonHandleBlock ι κ L 1)
      (frontier D \ (hamiltonAttachingBlock ι κ L (3 / 2) \
        hamiltonMarkedProjection ι κ L ''
          (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)))) := by
  obtain ⟨lift,hli,hsection,hcorefix,hpatchfix,_⟩ := b.exists_marked_standard_ball_lift hpos
  rcases b.position with ⟨hzero,_⟩ | ⟨_,hcore,_,_,hrel,hmark⟩
  · omega
  apply disjoint_left.mpr
  intro x hxCore hxLat
  have hxD := hcore hxCore
  have hxR := b.subset_domain hxD
  by_cases hxOld : x ∈ frontier (latticeHandleDomain ι κ L)
  · have hxAtt := hmark.subset ⟨hxD,hxOld⟩
    have hxRim : x ∈ hamiltonMarkedProjection ι κ L ''
        (sphere (0 : ι → ℝ) 1 ×ˢ sphere (0 : κ → ℝ) (3 / 2)) := by
      by_contra hn
      exact hxLat.2 ⟨hxAtt,hn⟩
    obtain ⟨z,hz,hzx⟩ := hxCore
    obtain ⟨w,hw,hwx⟩ := hxRim
    have hzw : z = w := (hcorefix ⟨x,hxD⟩ z hz hzx).symm.trans
      (hpatchfix ⟨x,hxD⟩ w ⟨hw.1,sphere_subset_closedBall hw.2⟩ hwx)
    have hzNorm := mem_closedBall_zero_iff.mp hz.2
    have hwNorm := mem_sphere_zero_iff_norm.mp hw.2
    rw [hzw] at hzNorm
    linarith
  · have hxIntR : x ∈ interior (latticeHandleDomain ι κ L) := by
      rw [←self_sdiff_frontier]
      exact ⟨hxR,hxOld⟩
    have hxRel := hrel (show (⟨x,hxR⟩ : latticeHandleDomain ι κ L) ∈
      (Subtype.val : latticeHandleDomain ι κ L → LatticeHandleAmbient ι κ L) ⁻¹'
        hamiltonHandleBlock ι κ L 1 from hxCore)
    exact hxLat.1.2 (mem_interior_of_relative_interior_at_interior ⟨x,hxR⟩ hxRel hxIntR)

end PoincareConjecture.M76
