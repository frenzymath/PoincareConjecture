import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Handles.BoundedSphereRegion
import PoincareConjecture.Proofs.M76.Mathlib.ContractibleBallExtension
import PoincareConjecture.Proofs.Horizon.Topology.Plane.Jordan.Domains
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.PlanarJordanSimpleConnectivity
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Protection.BoundaryDisks.JordanFillingCoverage

set_option autoImplicit false
open Set Metric Bornology

namespace PoincareConjecture.M76

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Q" => sphere (0 : Plane) 1
local notation "D2" => closedBall (0 : Fin 2 → ℝ) 1
local notation "Q2" => sphere (0 : Fin 2 → ℝ) 1

theorem exists_null_lattice_circle_region_in_filling
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ = 2)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    (g : C(D2, (κ → ℝ) ⧸ L.toAddSubgroup))
    (gamma : C(Q2, (κ → ℝ) ⧸ L.toAddSubgroup))
    (hinj : Function.Injective gamma)
    (hboundary : ∀ z : Q2, g ⟨z, sphere_subset_closedBall z.property⟩ = gamma z) :
    ∃ U : Set ((κ → ℝ) ⧸ L.toAddSubgroup),
      IsOpen U ∧ IsCompact (closure U) ∧
      frontier U = range gamma ∧ frontier (closure U) = frontier U ∧
      IsSimplyConnected U ∧ closure U ⊆ range g := by
  let a : Plane ≃L[ℝ] (κ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by simp [hκ])
  let p : Plane →+ ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    (QuotientAddGroup.mk' L.toAddSubgroup).comp a.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.comp_homeomorph a.toHomeomorph
  have hsurj : Function.Surjective p := QuotientAddGroup.mk_surjective.comp a.surjective
  let : ContractibleSpace D2 := contractibleSpace_closedBall zero_le_one
  let : LocallyPathConnectedSpace D2 := (convex_closedBall (0 : Fin 2 → ℝ) 1).locallyPathConnectedSpace
  let z0 : D2 := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨x0, hx0⟩ := hsurj (g z0)
  obtain ⟨G, ⟨_, hG⟩, _⟩ := hp.existsUnique_continuousMap_lifts g z0 x0 hx0
  let c : (Fin 2 → ℝ) ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c
  let inc : C(Q, D2) := ⟨fun z => ⟨H.symm z, sphere_subset_closedBall (H.symm z).property⟩,
    (continuous_subtype_val.comp H.symm.continuous).subtype_mk _⟩
  let l : C(Q, Plane) := G.comp inc
  have hl (z : Q) : p (l z) = gamma (H.symm z) :=
    (congrFun hG (inc z)).trans (hboundary (H.symm z))
  have hli : Function.Injective l := by
    intro x y hxy
    exact H.symm.injective (hinj ((hl x).symm.trans ((congrArg p hxy).trans (hl y))))
  obtain ⟨U, V, hU, hV, hUc, hVc, hUb, _, hdis, hcover, hUf, hVf, hK⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains l.continuous hli
  have hsc : IsSimplyConnected U := isSimplyConnected_bounded_jordan_side
    hU hUc.isConnected hUb hVc.isConnected hdis hcover hVf
  have hfill : closure U ⊆ range G :=
    closure_minimal (bounded_jordan_side_subset_filling G l hli inc (fun _ => rfl) hUb hUf)
      (isCompact_range G.continuous).isClosed
  have hfc : IsConnected (frontier U) := by
    rw [hUf]
    let : ConnectedSpace Q := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by rw [← Module.finrank_eq_rank]; simp) (0 : Plane) zero_le_one)
    exact isConnected_range l.continuous
  have hpi : InjOn p (frontier U) := by
    rw [hUf]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact congrArg l (H.symm.injective (hinj ((hl x).symm.trans (hxy.trans (hl y)))))
  have hKi : InjOn p (closure U) :=
    injOn_closure_of_injOn_connected_frontier p hU hUb hUc.isConnected hfc hpi
  have himage : p '' frontier U = range gamma := by
    rw [hUf]
    ext y
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨H.symm z, (hl z).symm⟩
    · rintro ⟨z, rfl⟩
      refine ⟨l (H z), mem_range_self _, ?_⟩
      simpa using hl (H z)
  have hlocal := hp.isLocalHomeomorph
  have hcl : closure (p '' U) = p '' closure U :=
    (image_closure_of_isCompact hK hp.continuous.continuousOn).symm
  have hclU : closure U = Vᶜ := by
    rw [closure_eq_self_union_frontier, hUf]
    ext x
    have hpartition : x ∈ U ∨ x ∈ V ↔ x ∉ range l := Set.ext_iff.mp hcover x
    constructor
    · rintro (hxU | hxL) hxV
      · exact disjoint_left.mp hdis hxU hxV
      · exact (hpartition.mp (Or.inr hxV)) hxL
    · intro hxV
      by_cases hxL : x ∈ range l
      · exact Or.inr hxL
      · exact Or.inl ((hpartition.mpr hxL).resolve_right hxV)
  have hclfront : frontier (closure U) = frontier U := by
    rw [hclU, frontier_compl, hVf, hUf]
  have hf : frontier (p '' U) = range gamma := by
    rw [(hlocal.isOpenMap _ hU).frontier_eq, hcl,
      ← hKi.image_sdiff_subset subset_closure, ← hU.frontier_eq, himage]
  refine ⟨p '' U, hlocal.isOpenMap _ hU, hcl ▸ hK.image hp.continuous, hf, ?_, ?_, ?_⟩
  · rw [hcl, frontier_image_compact_of_localHomeomorph hlocal hK hKi, hclfront, himage, hf]
  · let q : U → (κ → ℝ) ⧸ L.toAddSubgroup := fun x => p x
    have hq : IsLocalHomeomorph q :=
      hlocal.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hqi : Function.Injective q := fun x y hxy =>
      Subtype.ext (hKi (subset_closure x.property) (subset_closure y.property) hxy)
    have hrange : range q = p '' U := by
      ext y
      simp only [mem_range, mem_image, Subtype.exists, exists_prop, q]
    let J : U ≃ₜ (p '' U) :=
      (hq.isOpenEmbedding_of_injective hqi).isEmbedding.toHomeomorph.trans (Homeomorph.setCongr hrange)
    let : SimplyConnectedSpace U := hsc
    exact J.symm.toHomotopyEquiv.simplyConnectedSpace
  · rw [hcl]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨z, rfl⟩ := hfill hx
    exact ⟨z, (congrFun hG z).symm⟩

end PoincareConjecture.M76
