import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Phase.ResidualComponents
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Maps.Adjustments.CollarPhaseGroups









set_option autoImplicit false
open Set Geometry Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates


noncomputable def hamiltonZeroRetainedTangentialMap (phi : C(H0, H0)) (S : Set X0) :
    C(S, C0 × C0) :=
  ⟨fun z => (Q0 (hamiltonZeroAmbientMap phi z)).1, by fun_prop⟩



theorem FrontierResidualModel.isCoveringMap_installed_component
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {N S : Set X0}
    (M : FrontierResidualModel e N S) (phi : C(H0, H0))
    (H : E ≃ₜ S) (g : C(E, C0 × C0)) (hg : IsCoveringMap g)
    (hinstalled : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (H z))).1 = g z)
    (i : Fin M.count) :
    IsCoveringMap (hamiltonZeroRetainedTangentialMap phi (M.components i)) := by
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hwhole : IsCoveringMap (hamiltonZeroRetainedTangentialMap phi S) := by
    have heq : (hamiltonZeroRetainedTangentialMap phi S : S → C0 × C0) = g ∘ H.symm := by
      funext x
      simpa only [hamiltonZeroRetainedTangentialMap, ContinuousMap.coe_mk,
        Function.comp_apply, H.apply_symm_apply] using hinstalled (H.symm x)
    rw [heq]
    exact hg.comp_homeomorph H.symm
  exact M.isCoveringMap_component (hamiltonZeroRetainedTangentialMap phi S) hwhole i





theorem FrontierResidualModel.installed_boundary_component
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {N S U R : Set X0}
    (M : FrontierResidualModel e N S) (phi : C(H0, H0))
    (H : E ≃ₜ S) (g : C(E, C0 × C0)) (hg : IsCoveringMap g)
    (hinstalled : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (H z))).1 = g z)
    (hR : IsClosed R) (hU : IsClosed U) (hSU : Disjoint S U)
    (hfront : frontier R = S ∪ U) (i : Fin M.count) :
    let B : Set R := Subtype.val ⁻¹' M.components i
    let F : Set R := Subtype.val ⁻¹' frontier R
    IsCompact B ∧ IsConnected B ∧ B ⊆ F ∧
      IsClopen ((Subtype.val : F → R) ⁻¹' B) ∧
      ∃ gB : C(B, C0 × C0), IsCoveringMap gB ∧
        ∀ x : B, (hamiltonZeroRetainedTangentialMap phi R) x = gB x := by
  classical
  intro B F
  let : T2Space X0 := (Q0).isEmbedding.t2Space
  have hSF : S ⊆ frontier R := hfront.symm ▸ subset_union_left
  have hSR : M.components i ⊆ R :=
    ((M.component i).2.2.1.trans hSF).trans hR.frontier_subset
  let J : M.components i ≃ₜ B := {
    toFun := fun z => ⟨⟨z, hSR z.property⟩, z.property⟩
    invFun := fun z => ⟨z.1.1, z.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }
  let inc : C(M.components i, R) := ⟨fun z => ⟨z, hSR z.property⟩, by fun_prop⟩
  have hrange : range inc = B := by
    ext x
    constructor
    · rintro ⟨z, rfl⟩
      exact z.property
    · intro hx
      exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩
  let : CompactSpace (M.components i) := isCompact_iff_compactSpace.mp (M.component i).1
  let : ConnectedSpace (M.components i) := isConnected_iff_connectedSpace.mp (M.component i).2.1
  have hBc : IsCompact B := hrange ▸ isCompact_range inc.continuous
  have hBn : IsConnected B := hrange ▸ isConnected_range inc.continuous
  have hBF : B ⊆ F := fun _ hx => hSF ((M.component i).2.2.1 hx)
  let T : Set X0 := U ∪ ⋃ k : Fin M.count, if k = i then ∅ else M.components k
  have hT : IsClosed T := hU.union (isClosed_iUnion_of_finite fun k => by
    split_ifs
    · exact isClosed_empty
    · exact (M.component k).1.isClosed)
  have hcompl : (Subtype.val : F → R) ⁻¹' B =
      (fun z : F => (z.1 : X0)) ⁻¹' Tᶜ := by
    ext z
    change (z.1 : X0) ∈ M.components i ↔ (z.1 : X0) ∉ T
    constructor
    · intro hz ht
      rcases ht with hu | ht
      · exact disjoint_left.mp hSU ((M.component i).2.2.1 hz) hu
      · obtain ⟨k, hk⟩ := mem_iUnion.mp ht
        by_cases hki : k = i
        · simp [hki] at hk
        · have hk' : (z.1 : X0) ∈ M.components k := by simpa [hki] using hk
          exact disjoint_left.mp (M.disjoint hki) hk' hz
    · intro hz
      have hzF : (z.1 : X0) ∈ S ∪ U := hfront ▸ z.property
      rcases hzF with hs | hu
      · obtain ⟨k, hk⟩ := mem_iUnion.mp (M.cover.symm ▸ hs)
        by_cases hki : k = i
        · exact hki ▸ hk
        · exact False.elim (hz (Or.inr (mem_iUnion.mpr ⟨k, by simpa [hki] using hk⟩)))
      · exact False.elim (hz (Or.inl hu))
  have hclopen : IsClopen ((Subtype.val : F → R) ⁻¹' B) := by
    refine ⟨hBc.isClosed.preimage continuous_subtype_val, ?_⟩
    rw [hcompl]
    exact hT.isOpen_compl.preimage (by fun_prop)
  let gB : C(B, C0 × C0) :=
    (hamiltonZeroRetainedTangentialMap phi (M.components i)).comp ⟨J.symm, J.symm.continuous⟩
  exact ⟨hBc, hBn, hBF, hclopen, gB,
    (M.isCoveringMap_installed_component phi H g hg hinstalled i).comp_homeomorph J.symm,
    fun _ => rfl⟩




theorem FrontierResidualModel.installed_boundary_component_of_collar
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 V3} {N S U R : Set X0}
    (M : FrontierResidualModel e N S) (phi : C(H0, H0))
    (H : E ≃ₜ S) (g : C(E, C0 × C0)) (hg : IsCoveringMap g)
    (c : E × ℝ → X0) (hzero : ∀ z, c (z, 0) = H z)
    {r : ℝ} (hr : 0 ≤ r) (theta : C0) (sigma : ℝ)
    (hproduct : ∀ z, ∀ t ∈ Icc (-r) r,
      Q0 (hamiltonZeroAmbientMap phi (c (z, t))) =
        (g z, theta + ((sigma * t : ℝ) : C0)))
    (hR : IsClosed R) (hU : IsClosed U) (hSU : Disjoint S U)
    (hfront : frontier R = S ∪ U) (i : Fin M.count) :
    let B : Set R := Subtype.val ⁻¹' M.components i
    let F : Set R := Subtype.val ⁻¹' frontier R
    IsCompact B ∧ IsConnected B ∧ B ⊆ F ∧
      IsClopen ((Subtype.val : F → R) ⁻¹' B) ∧
      (∀ x : B, (Q0 (hamiltonZeroAmbientMap phi (x.1 : X0))).2 = theta) ∧
      ∃ gB : C(B, C0 × C0), IsCoveringMap gB ∧
        ∀ x : B, (hamiltonZeroRetainedTangentialMap phi R) x = gB x := by
  intro B F
  have hbase (z : E) : Q0 (hamiltonZeroAmbientMap phi (H z)) = (g z, theta) := by
    have h := hproduct z 0 ⟨neg_nonpos.mpr hr, hr⟩
    rw [hzero, mul_zero, AddCircle.coe_zero, add_zero] at h
    exact h
  obtain ⟨hBc, hBn, hBF, hclopen, gB, hgB, hgBval⟩ :=
    M.installed_boundary_component phi H g hg (fun z => congrArg Prod.fst (hbase z))
      hR hU hSU hfront i
  refine ⟨hBc, hBn, hBF, hclopen, ?_, gB, hgB, hgBval⟩
  intro x
  let y : S := ⟨(x.1 : X0), (M.component i).2.2.1 x.property⟩
  have h := congrArg Prod.snd (hbase (H.symm y))
  simpa only [H.apply_symm_apply] using h

end PoincareConjecture.M76
