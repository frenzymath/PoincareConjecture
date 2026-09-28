import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Regions.SourcePhaseResidualModels

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76.HamiltonIntervalTorus

local notation "V3" => (Fin 3 → ℝ)

theorem residualModel_component_in_subtype
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {N F : Set X}
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (x : F) (hx : (x : X) ∈ M.components i) :
    connectedComponent x = (Subtype.val : F → X) ⁻¹' M.components i := by
  apply (Set.image_injective.mpr Subtype.val_injective)
  rw [← connectedComponentIn_eq_image x.property, (M.component i).2.2.2 x hx,
    Subtype.image_preimage_coe, inter_eq_right.mpr (M.component i).2.2.1]

theorem exists_residualModel_component_equiv
    {X Y ι κ : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {e : ι → OpenPartialHomeomorph X V3} {d : κ → OpenPartialHomeomorph Y V3}
    {N F : Set X} {N' F' : Set Y}
    (M : FrontierResidualModel e N F) (M' : FrontierResidualModel d N' F')
    (H : F ≃ₜ F') :
    ∃ r : Fin M.count ≃ Fin M'.count,
      ∀ (i : Fin M.count) (x : F), (x : X) ∈ M.components i ↔
        (H x : Y) ∈ M'.components (r i) := by
  classical
  have hex (i : Fin M.count) : ∃ j : Fin M'.count,
      ∀ x : F, (x : X) ∈ M.components i ↔ (H x : Y) ∈ M'.components j := by
    obtain ⟨x0, hx0⟩ := (M.component i).2.1.nonempty
    let x : F := ⟨x0, (M.component i).2.2.1 hx0⟩
    obtain ⟨j, hj⟩ := mem_iUnion.mp (M'.cover.symm.subset (H x).property)
    have hS := residualModel_component_in_subtype M i x hx0
    have hT := residualModel_component_in_subtype M' j (H x) hj
    refine ⟨j, ?_⟩
    intro y
    constructor
    · intro hy
      have hyC : y ∈ connectedComponent x := hS.symm.subset hy
      exact hT.subset (H.continuous.mapsTo_connectedComponent x hyC)
    · intro hy
      have hyC : H y ∈ connectedComponent (H x) := hT.symm.subset hy
      have h := H.symm.continuous.mapsTo_connectedComponent (H x) hyC
      change y ∈ (Subtype.val : F → X) ⁻¹' M.components i
      exact hS.subset (by simpa only [H.symm_apply_apply] using h)
  choose f hf using hex
  have hfi : Function.Injective f := by
    intro i j hij
    obtain ⟨x0, hx0⟩ := (M.component i).2.1.nonempty
    let x : F := ⟨x0, (M.component i).2.2.1 hx0⟩
    have hxj : (x : X) ∈ M.components j := (hf j x).mpr (hij ▸ (hf i x).mp hx0)
    by_contra hne
    exact disjoint_left.mp (M.disjoint hne) hx0 hxj
  have hfs : Function.Surjective f := by
    intro j
    obtain ⟨y0, hy0⟩ := (M'.component j).2.1.nonempty
    let y : F' := ⟨y0, (M'.component j).2.2.1 hy0⟩
    obtain ⟨i, hi⟩ := mem_iUnion.mp (M.cover.symm.subset (H.symm y).property)
    refine ⟨i, ?_⟩
    have hyi : (y : Y) ∈ M'.components (f i) := by
      simpa only [H.apply_symm_apply] using (hf i (H.symm y)).mp hi
    by_contra hne
    exact disjoint_left.mp (M'.disjoint hne) hyi hy0
  exact ⟨Equiv.ofBijective f ⟨hfi, hfs⟩, hf⟩

end PoincareConjecture.M76.HamiltonIntervalTorus
