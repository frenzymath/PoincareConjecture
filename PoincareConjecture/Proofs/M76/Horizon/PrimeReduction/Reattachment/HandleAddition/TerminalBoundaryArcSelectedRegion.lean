import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcJordanSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Reattachment.HandleAddition.TerminalBoundaryArcQuotientSide
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundedSphereRegion
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Domains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.PlanarJordanSimpleConnectivity

set_option autoImplicit false
open Set Metric
namespace PoincareConjecture.M76
local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Circle" => sphere (0 : Plane) 1

theorem exists_selected_quotient_jordan_region
    {Y : Type*} [AddCommGroup Y] [TopologicalSpace Y] [T2Space Y]
    (p : Plane →+ Y) (hp : IsCoveringMap p)
    (gamma delta : C(Circle,Plane))
    (hgamma : Function.Injective gamma) (hdelta : Function.Injective delta)
    (hpi : InjOn p (range gamma ∪ range delta))
    {T W C0 C1 : Set Plane} (hT : IsPreconnected T)
    (havoid : Disjoint (p '' (range gamma ∪ range delta)) (p '' T))
    (hg : range gamma = W ∪ C0) (hd : range delta = W ∪ C1)
    (hC0 : C0 ⊆ closure T) (hC1 : C1 ⊆ closure T)
    (hmark0 : (range gamma ∩ closure T).Nonempty)
    (hmark1 : (range delta ∩ closure T).Nonempty)
    (hdiff : range gamma ≠ range delta) :
    ∃ U : Set Plane, IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      IsSimplyConnected U ∧ interior (closure U) = U ∧
      (frontier U = range gamma ∨ frontier U = range delta) ∧
      InjOn p (closure U) ∧ Disjoint (p '' closure U) (p '' T) ∧
      IsOpen (p '' U) ∧ IsSimplyConnected (p '' U) ∧
      closure (p '' U) = p '' closure U ∧
      frontier (p '' U) = p '' frontier U := by
  have havoid0 : Disjoint T (range gamma) := by
    apply disjoint_left.mpr
    intro x hx hg
    exact disjoint_left.mp havoid (mem_image_of_mem p (Or.inl hg)) (mem_image_of_mem p hx)
  have havoid1 : Disjoint T (range delta) := by
    apply disjoint_left.mpr
    intro x hx hd
    exact disjoint_left.mp havoid (mem_image_of_mem p (Or.inr hd)) (mem_image_of_mem p hx)
  obtain ⟨U,hU,hUc,hK,hsc,hreg,hfront,hdis⟩ :=
    exists_jordan_side_avoiding_common_rim_disk hgamma hdelta hT havoid0 havoid1
      hg hd hC0 hC1 hdiff
  have hfs : frontier U ⊆ range gamma ∪ range delta := by
    rcases hfront with hh | hh
    · exact hh ▸ subset_union_left
    · exact hh ▸ subset_union_right
  let : ConnectedSpace Circle := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [←Module.finrank_eq_rank,finrank_euclideanSpace_fin];norm_num)
      (0 : Plane) zero_le_one)
  have hfc : IsConnected (frontier U) := by
    rcases hfront with hh | hh
    · exact hh ▸ isConnected_range gamma.continuous
    · exact hh ▸ isConnected_range delta.continuous
  have hKi : InjOn p (closure U) := injOn_closure_of_injOn_connected_frontier
    p hU (hK.isBounded.subset subset_closure) hUc hfc (hpi.mono hfs)
  have hmark : (frontier U ∩ closure T).Nonempty := by
    rcases hfront with hh | hh
    · exact hh ▸ hmark0
    · exact hh ▸ hmark1
  have hdisq := disjoint_image_of_injective_closed_side p hU hT hKi hdis
    (havoid.mono_left (image_mono hfs)) hmark
  have hlocal := hp.isLocalHomeomorph
  have hopen : IsOpen (p '' U) := hlocal.isOpenMap _ hU
  have hcl : closure (p '' U) = p '' closure U :=
    (image_closure_of_isCompact hK hp.continuous.continuousOn).symm
  refine ⟨U,hU,hUc,hK,hsc,hreg,hfront,hKi,hdisq,hopen,?_,hcl,?_⟩
  · let q : U → Y := fun x => p x
    have hq : IsLocalHomeomorph q :=
      hlocal.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hqi : Function.Injective q := fun x y hh =>
      Subtype.ext (hKi (subset_closure x.property) (subset_closure y.property) hh)
    have hrange : range q = p '' U := by
      ext y
      constructor
      · rintro ⟨x,rfl⟩; exact ⟨x,x.property,rfl⟩
      · rintro ⟨x,hx,rfl⟩; exact ⟨⟨x,hx⟩,rfl⟩
    let H : U ≃ₜ (p '' U) :=
      (hq.isOpenEmbedding_of_injective hqi).isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hrange)
    let : SimplyConnectedSpace U := hsc
    exact H.symm.toHomotopyEquiv.simplyConnectedSpace
  · rw [hopen.frontier_eq,hcl,←hKi.image_sdiff_subset subset_closure,←hU.frontier_eq]

end PoincareConjecture.M76
