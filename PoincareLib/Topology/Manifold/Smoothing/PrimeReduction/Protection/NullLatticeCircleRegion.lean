import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Handles.BoundedSphereRegion
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.ContractibleBallExtension
import PoincareLib.Topology.Plane.Jordan.Domains
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Protection.PlanarJordanSimpleConnectivity

/-!
# Bounded regions of null circles in lattice tori

A nullhomotopy lifts the actual circle to the plane. Jordan separation and
injectivity on the connected frontier then descend its entire bounded region.
No compatibility between the original PL atlas and the standard lattice atlas
is assumed. The bounded side is proved simply connected by contracting polygonal loop
approximations. This precedes original PL disk recognition; no disk
parametrization is asserted here.
-/

set_option autoImplicit false
open Set Metric

namespace PoincareMT.M76

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "Circle" => sphere (0 : Plane) 1

theorem exists_injective_null_circle_lift
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {p : X → Y} (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (gamma : C(Circle, Y)) (hinj : Function.Injective gamma)
    (hnull : gamma.Nullhomotopic) :
    ∃ l : C(Circle, X), Function.Injective l ∧ ∀ z, p (l z) = gamma z := by
  let D := closedBall (0 : Plane) 1
  let : ContractibleSpace D := contractibleSpace_closedBall zero_le_one
  let : LocallyPathConnectedSpace D := (convex_closedBall (0 : Plane) 1).locallyPathConnectedSpace
  obtain ⟨g, hg⟩ := hnull.exists_closedBall_extension gamma
  let z0 : D := ⟨0, mem_closedBall_self zero_le_one⟩
  obtain ⟨x0, hx0⟩ := hsurj (g z0)
  obtain ⟨G, ⟨_, hG⟩, _⟩ := hp.existsUnique_continuousMap_lifts g z0 x0 hx0
  let inc : Circle → D := fun z => ⟨z, sphere_subset_closedBall z.property⟩
  let l : C(Circle, X) := ⟨fun z => G (inc z), G.continuous.comp (by fun_prop)⟩
  have hl (z : Circle) : p (l z) = gamma z :=
    (congrFun hG (inc z)).trans (hg z)
  refine ⟨l, ?_, hl⟩
  intro x y hxy
  exact hinj ((hl x).symm.trans ((congrArg p hxy).trans (hl y)))

theorem exists_null_circle_bounded_region_with_simplyConnected
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    (p : Plane →+ Y) (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    (gamma : C(Circle, Y)) (hinj : Function.Injective gamma)
    (hnull : gamma.Nullhomotopic) :
    ∃ U : Set Plane, IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      IsConnected (frontier U) ∧ InjOn p (closure U) ∧
      p '' frontier U = range gamma ∧
      IsOpen (p '' U) ∧ IsConnected (p '' U) ∧
      closure (p '' U) = p '' closure U ∧
      frontier (p '' U) = range gamma ∧
      frontier (p '' closure U) = range gamma ∧
      IsSimplyConnected U ∧ IsSimplyConnected (p '' U) := by
  obtain ⟨l, hli, hl⟩ := exists_injective_null_circle_lift hp hsurj gamma hinj hnull
  obtain ⟨U, V, hU, hV, hUc, hVc, hUb, _, hdis, hcover, hUf, hVf, hK⟩ :=
    Poincare.Topology.Plane.Jordan.exists_complementary_domains l.continuous hli
  have hfc : IsConnected (frontier U) := by
    rw [hUf]
    let : ConnectedSpace Circle := isConnected_iff_connectedSpace.mp
      (isConnected_sphere (by
        rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
        norm_num) (0 : Plane) zero_le_one)
    exact isConnected_range l.continuous
  have hpi : InjOn p (frontier U) := by
    rw [hUf]
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ hxy
    exact congrArg l (hinj ((hl x).symm.trans (hxy.trans (hl y))))
  have hKi : InjOn p (closure U) :=
    injOn_closure_of_injOn_connected_frontier p hU hUb hUc.isConnected hfc hpi
  have himage : p '' frontier U = range gamma := by
    rw [hUf]
    ext y
    constructor
    · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
      exact ⟨z, (hl z).symm⟩
    · rintro ⟨z, rfl⟩
      exact ⟨l z, mem_range_self z, hl z⟩
  have hsc : IsSimplyConnected U := isSimplyConnected_bounded_jordan_side
    hU hUc.isConnected hUb hVc.isConnected hdis hcover hVf
  have hlocal := hp.isLocalHomeomorph
  have hcl : closure (p '' U) = p '' closure U :=
    (image_closure_of_isCompact hK hp.continuous.continuousOn).symm
  have hclU : closure U = Vᶜ := by
    rw [closure_eq_self_union_frontier, hUf]
    ext x
    have hpartition : x ∈ U ∨ x ∈ V ↔ x ∉ range l := by
      exact Set.ext_iff.mp hcover x
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
  refine ⟨U, hU, hUc.isConnected, hK, hfc, hKi, himage,
    hlocal.isOpenMap _ hU, hUc.isConnected.image p hp.continuous.continuousOn, hcl, ?_, ?_, hsc, ?_⟩
  · rw [(hlocal.isOpenMap _ hU).frontier_eq, hcl,
      ← hKi.image_sdiff_subset subset_closure, ← hU.frontier_eq, himage]
  · rw [frontier_image_compact_of_localHomeomorph hlocal hK hKi, hclfront, himage]
  · let q : U → Y := fun x => p x
    have hq : IsLocalHomeomorph q :=
      hlocal.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph
    have hqi : Function.Injective q := by
      intro x y hxy
      exact Subtype.ext (hKi (subset_closure x.property) (subset_closure y.property) hxy)
    have hrange : range q = p '' U := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, x.property, rfl⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    let H : U ≃ₜ (p '' U) :=
      (hq.isOpenEmbedding_of_injective hqi).isEmbedding.toHomeomorph.trans
        (Homeomorph.setCongr hrange)
    let : SimplyConnectedSpace U := hsc
    exact H.symm.toHomotopyEquiv.simplyConnectedSpace

theorem exists_null_lattice_circle_region_with_simplyConnected
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ = 2)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    (gamma : C(sphere (0 : Fin 2 → ℝ) 1, (κ → ℝ) ⧸ L.toAddSubgroup))
    (hinj : Function.Injective gamma) (hnull : gamma.Nullhomotopic) :
    ∃ U : Set ((κ → ℝ) ⧸ L.toAddSubgroup),
      IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      frontier U = range gamma ∧ frontier (closure U) = range gamma ∧ IsSimplyConnected U := by
  let a : Plane ≃L[ℝ] (κ → ℝ) := ContinuousLinearEquiv.ofFinrankEq (by
    simp [hκ])
  let p : Plane →+ ((κ → ℝ) ⧸ L.toAddSubgroup) :=
    (QuotientAddGroup.mk' L.toAddSubgroup).comp a.toLinearEquiv.toAddEquiv.toAddMonoidHom
  have hp : IsCoveringMap p :=
    (L.toAddSubgroup.isAddQuotientCoveringMap_of_comm
      DiscreteTopology.isDiscrete).isCoveringMap.comp_homeomorph a.toHomeomorph
  have hsurj : Function.Surjective p := QuotientAddGroup.mk_surjective.comp a.surjective
  let c : (Fin 2 → ℝ) ≃L[ℝ] Plane := ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareMT.Proofs.M02.Topology.unitSphereHomeomorph c
  let h : C(Circle, sphere (0 : Fin 2 → ℝ) 1) := ⟨H.symm, H.symm.continuous⟩
  let g : C(Circle, (κ → ℝ) ⧸ L.toAddSubgroup) := gamma.comp h
  have hg : range g = range gamma := by
    change range (gamma ∘ H.symm) = range gamma
    exact H.symm.surjective.range_comp gamma
  obtain ⟨U, hU, hUc, hK, _, _, _, hO, hOc, hcl, hf, hcf, _, hsc⟩ :=
    exists_null_circle_bounded_region_with_simplyConnected p hp hsurj g (hinj.comp H.symm.injective)
      (hnull.comp_left h)
  refine ⟨p '' U, hO, hOc, hcl ▸ hK.image hp.continuous, ?_, ?_, hsc⟩
  · exact hf.trans hg
  · rw [hcl]
    exact hcf.trans hg


theorem exists_null_circle_bounded_region
    {Y : Type*} [AddGroup Y] [TopologicalSpace Y] [T2Space Y]
    (p : EuclideanSpace ℝ (Fin 2) →+ Y) (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p)
    (gamma : C(sphere (0 : EuclideanSpace ℝ (Fin 2)) 1, Y))
    (hinj : Function.Injective gamma) (hnull : gamma.Nullhomotopic) :
    ∃ U : Set (EuclideanSpace ℝ (Fin 2)), IsOpen U ∧ IsConnected U ∧
      IsCompact (closure U) ∧ IsConnected (frontier U) ∧ InjOn p (closure U) ∧
      p '' frontier U = range gamma ∧
      IsOpen (p '' U) ∧ IsConnected (p '' U) ∧
      closure (p '' U) = p '' closure U ∧
      frontier (p '' U) = range gamma ∧
      frontier (p '' closure U) = range gamma := by
  obtain ⟨U, hU, hc, hK, hfc, hi, hfr, hO, hOc, hcl, hf, hcf, _, _⟩ :=
    exists_null_circle_bounded_region_with_simplyConnected p hp hsurj gamma hinj hnull
  exact ⟨U, hU, hc, hK, hfc, hi, hfr, hO, hOc, hcl, hf, hcf⟩

theorem exists_null_lattice_circle_region
    {κ : Type*} [Fintype κ] (hκ : Fintype.card κ = 2)
    (L : Submodule ℤ (κ → ℝ)) [DiscreteTopology L]
    (gamma : C(sphere (0 : Fin 2 → ℝ) 1, (κ → ℝ) ⧸ L.toAddSubgroup))
    (hinj : Function.Injective gamma) (hnull : gamma.Nullhomotopic) :
    ∃ U : Set ((κ → ℝ) ⧸ L.toAddSubgroup),
      IsOpen U ∧ IsConnected U ∧ IsCompact (closure U) ∧
      frontier U = range gamma ∧ frontier (closure U) = range gamma := by
  obtain ⟨U, hU, hc, hK, hf, hcf, _⟩ :=
    exists_null_lattice_circle_region_with_simplyConnected hκ L gamma hinj hnull
  exact ⟨U, hU, hc, hK, hf, hcf⟩

end PoincareMT.M76
