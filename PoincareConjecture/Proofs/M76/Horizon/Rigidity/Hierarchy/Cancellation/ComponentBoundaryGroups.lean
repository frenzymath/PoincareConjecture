import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.InstalledBoundaryCoverings
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.BoundaryLoopPowers











set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76

theorem boundary_group_finiteIndex_of_covering_composite
    {E X T : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [TopologicalSpace T] [CompactSpace E] [T1Space T]
    (i : C(E, X)) (f : C(X, T)) (hcover : IsCoveringMap (f.comp i))
    (x : E) (hinj : Function.Injective (FundamentalGroup.map f (i x))) :
    (FundamentalGroup.map i x).range.FiniteIndex := by
  have hc := hcover.fundamentalGroup_range_finiteIndex_of_compact x
  change (FundamentalGroup.map (f.comp i) x).range.FiniteIndex at hc
  rw [FundamentalGroup.map_comp, MonoidHom.range_comp] at hc
  have hindex := hc.index_ne_zero
  rw [(FundamentalGroup.map i x).range.index_map_of_injective hinj] at hindex
  exact ⟨fun h => hindex (by rw [h, zero_mul])⟩

theorem boundary_groups_commensurable_of_finiteIndex
    {E₀ E₁ X : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace X]
    (i₀ : C(E₀, X)) (i₁ : C(E₁, X)) (x₀ : E₀) (x₁ : E₁)
    (h₀ : (FundamentalGroup.map i₀ x₀).range.FiniteIndex)
    (h₁ : (FundamentalGroup.map i₁ x₁).range.FiniteIndex)
    (k : Path (i₀ x₀) (i₁ x₁)) :
    (FundamentalGroup.map i₀ x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ x₁)).range := by
  let := h₀
  let := h₁
  let T := FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm
  have htransport : ((T.toMonoidHom).comp (FundamentalGroup.map i₁ x₁)).range.FiniteIndex := by
    rw [MonoidHom.range_comp]
    constructor
    rw [Subgroup.index_map_of_bijective (f := T.toMonoidHom) T.bijective]
    exact h₁.index_ne_zero
  let := htransport
  exact ⟨Subgroup.isFiniteRelIndex_of_finiteIndex.relIndex_ne_zero,
    Subgroup.isFiniteRelIndex_of_finiteIndex.relIndex_ne_zero⟩

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZeroRetainedTangentialMap_pi1_injective
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {R : Set X0} {cut a b : ℝ}
    (ha : cut < a) (hab : a ≤ b) (hb : b < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (x : R)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x)) :
    Function.Injective (FundamentalGroup.map (hamiltonZeroRetainedTangentialMap phi R) x) := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let coords : C(H0, (C0 × C0) × C0) := hamiltonZeroHierarchyCoordinates
  let inc : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let f := coords.comp (phi.comp (ambient.comp inc))
  have hf : Function.Injective (FundamentalGroup.map f x) := by
    change Function.Injective (FundamentalGroup.map
      (coords.comp (phi.comp (ambient.comp inc))) x)
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroHierarchyCoordinates.fundamentalGroupMulEquiv
      (phi (ambient x))).injective.comp
      ((F.fundamentalGroup_map_bijective (ambient x)).1.comp
        ((hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv x).injective.comp hinj))
  obtain ⟨H, _⟩ := AddCircle.exists_shifted_closedArc_normal_contraction p ha hb
    (show a ∈ Icc a b from ⟨le_rfl, hab⟩) f (fun y => hR y.property)
  let j : C(C0 × C0, (C0 × C0) × C0) :=
    ⟨fun z => (z, (a : C0)), continuous_id.prodMk continuous_const⟩
  have heq : j.comp (hamiltonZeroRetainedTangentialMap phi R) =
      ⟨fun y => ((f y).1, (a : C0)), f.continuous.fst.prodMk continuous_const⟩ := by
    apply ContinuousMap.ext
    intro y
    rfl
  have hg := FundamentalGroup.map_injective_of_homotopy H.toHomotopy x hf
  rw [← heq, FundamentalGroup.map_comp] at hg
  exact Function.Injective.of_comp hg

theorem FrontierResidualModel.installed_component_group_finiteIndex
    {E ι : Type*} [TopologicalSpace E]
    {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)} {N S R : Set X0}
    (M : FrontierResidualModel e N S)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {cut a b : ℝ} (ha : cut < a) (hab : a ≤ b) (hb : b < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (H : E ≃ₜ S) (g : C(E, C0 × C0)) (hg : IsCoveringMap g)
    (hinstalled : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (H z))).1 = g z)
    (i : Fin M.count) (hsub : M.components i ⊆ R) (x : M.components i)
    (hinj : Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) (ContinuousMap.inclusion hsub x))) :
    (FundamentalGroup.map (ContinuousMap.inclusion hsub) x).range.FiniteIndex := by
  let : CompactSpace (M.components i) := isCompact_iff_compactSpace.mp (M.component i).1
  have hc : IsCoveringMap ((hamiltonZeroRetainedTangentialMap phi R).comp
      (ContinuousMap.inclusion hsub)) :=
    M.isCoveringMap_installed_component phi H g hg hinstalled i
  exact boundary_group_finiteIndex_of_covering_composite
    (ContinuousMap.inclusion hsub) (hamiltonZeroRetainedTangentialMap phi R) hc x
    (hamiltonZeroRetainedTangentialMap_pi1_injective phi F ha hab hb hR _ hinj)




theorem hamiltonZero_installed_component_boundary_groups
    {E₀ E₁ ι : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    {e : ι → OpenPartialHomeomorph X0 (Fin 3 → ℝ)} {N₀ N₁ S₀ S₁ R : Set X0}
    (M₀ : FrontierResidualModel e N₀ S₀) (M₁ : FrontierResidualModel e N₁ S₁)
    (phi : C(H0, H0)) (F : (ContinuousMap.id H0).HomotopyRel phi B0)
    {cut a b : ℝ} (ha : cut < a) (hab : a ≤ b) (hb : b < cut + p)
    (hR : R ⊆ hamiltonZeroCircleMap phi ⁻¹' AddCircle.closedIntervalArc p a b)
    (hinj : ∀ x : R, Function.Injective (FundamentalGroup.map
      (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) x))
    (H₀ : E₀ ≃ₜ S₀) (H₁ : E₁ ≃ₜ S₁)
    (g₀ : C(E₀, C0 × C0)) (g₁ : C(E₁, C0 × C0))
    (hg₀ : IsCoveringMap g₀) (hg₁ : IsCoveringMap g₁)
    (hinstalled₀ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (H₀ z))).1 = g₀ z)
    (hinstalled₁ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (H₁ z))).1 = g₁ z)
    (i₀ : Fin M₀.count) (i₁ : Fin M₁.count)
    (hsub₀ : M₀.components i₀ ⊆ R) (hsub₁ : M₁.components i₁ ⊆ R)
    (x₀ : M₀.components i₀) (x₁ : M₁.components i₁) :
    let inc₀ := ContinuousMap.inclusion hsub₀
    let inc₁ := ContinuousMap.inclusion hsub₁
    (FundamentalGroup.map inc₀ x₀).range.FiniteIndex ∧
    (FundamentalGroup.map inc₁ x₁).range.FiniteIndex ∧
    ∀ k : Path (inc₀ x₀) (inc₁ x₁),
      (FundamentalGroup.map inc₀ x₀).range.Commensurable
        (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
          (FundamentalGroup.map inc₁ x₁)).range ∧
      ∀ alpha : Path x₀ x₀, ∃ n : ℕ, 0 < n ∧ ∃ beta : Path x₁ x₁,
        ((boundaryLoopIterate alpha n).map inc₀.continuous).Homotopic
          (k.trans ((beta.map inc₁.continuous).trans k.symm)) := by
  intro inc₀ inc₁
  have h₀ := M₀.installed_component_group_finiteIndex phi F ha hab hb hR H₀ g₀ hg₀
    hinstalled₀ i₀ hsub₀ x₀ (hinj _)
  have h₁ := M₁.installed_component_group_finiteIndex phi F ha hab hb hR H₁ g₁ hg₁
    hinstalled₁ i₁ hsub₁ x₁ (hinj _)
  refine ⟨h₀, h₁, fun k => ?_⟩
  have hcomm := boundary_groups_commensurable_of_finiteIndex inc₀ inc₁ x₀ x₁ h₀ h₁ k
  exact ⟨hcomm, fun alpha => exists_boundary_loop_power_homotopy inc₀ inc₁ x₀ x₁ k hcomm alpha⟩

end PoincareConjecture.M76
