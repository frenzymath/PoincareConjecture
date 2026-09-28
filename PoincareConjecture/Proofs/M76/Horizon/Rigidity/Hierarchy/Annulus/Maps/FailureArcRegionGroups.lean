import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FailureArcBoundaryGroups









set_option autoImplicit false
open Set

namespace PoincareConjecture.M76

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates



theorem hamiltonZero_region_boundary_groups_commensurable_of_failure_arc
    {E₀ E₁ : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [CompactSpace E₀] [CompactSpace E₁]
    (phi : C(H0, H0)) (F₀ : (ContinuousMap.id H0).HomotopyRel phi B0)
    (R : Set X0) (i₀ : C(E₀, R)) (i₁ : C(E₁, R))
    (g₀ : C(E₀, C0 × C0)) (g₁ : C(E₁, C0 × C0))
    (hg₀ : IsCoveringMap g₀) (hg₁ : IsCoveringMap g₁) (delta₀ delta₁ : C0)
    (htangent₀ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₀ z))).1 = g₀ z)
    (htangent₁ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₁ z))).1 = g₁ z)
    (hnormal₀ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₀ z))).2 = delta₀)
    (hnormal₁ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₁ z))).2 = delta₁)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hinjR : Function.Injective
      (FundamentalGroup.map (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0)) (i₀ e₀)))
    (F : (((hamiltonZeroAmbientMap phi).comp
        (⟨Subtype.val, continuous_subtype_val⟩ : C(R, X0))).comp k.toContinuousMap).HomotopyRel
      (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (i₀ e₀)))
      ({0, 1} : Set unitInterval)) :
    delta₀ = delta₁ ∧ (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  let inclusion : C(R, X0) := ⟨Subtype.val, continuous_subtype_val⟩
  let f := (hamiltonZeroAmbientMap phi).comp inclusion
  have hends : f (i₁ e₁) = f (i₀ e₀) := by
    have hh := F.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl)
    change f (k 1) = f (i₀ e₀) at hh
    simpa only [Path.target] using hh
  have hlabels : delta₁ = delta₀ := (hnormal₁ e₁).symm.trans
    ((congrArg (fun z => (Q0 z).2) hends).trans (hnormal₀ e₀))
  refine ⟨hlabels.symm, ?_⟩
  subst delta₁
  let j : C(C0 × C0, X0) := ⟨fun z => (Q0).symm (z, delta₀), by fun_prop⟩
  have hj : Function.Injective j := by
    intro x y hxy
    exact congrArg Prod.fst ((Q0).symm.injective hxy)
  have h₀ : f.comp i₀ = j.comp g₀ := by
    apply ContinuousMap.ext
    intro z
    apply (Q0).injective
    change Q0 (hamiltonZeroAmbientMap phi (i₀ z)) = Q0 ((Q0).symm (g₀ z, delta₀))
    rw [(Q0).apply_symm_apply]
    exact Prod.ext (htangent₀ z) (hnormal₀ z)
  have h₁ : f.comp i₁ = j.comp g₁ := by
    apply ContinuousMap.ext
    intro z
    apply (Q0).injective
    change Q0 (hamiltonZeroAmbientMap phi (i₁ z)) = Q0 ((Q0).symm (g₁ z, delta₀))
    rw [(Q0).apply_symm_apply]
    exact Prod.ext (htangent₁ z) (hnormal₁ z)
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let inverse : C(H0, X0) := hamiltonZeroAmbientEquiv.symm
  have hinjAmbient : Function.Injective
      (FundamentalGroup.map (hamiltonZeroAmbientMap phi) (i₀ e₀)) := by
    change Function.Injective
      (FundamentalGroup.map (inverse.comp (phi.comp ambient)) (i₀ e₀))
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroAmbientEquiv.symm.fundamentalGroupMulEquiv
      (phi (ambient (i₀ e₀)))).injective.comp
      ((F₀.fundamentalGroup_map_bijective (ambient (i₀ e₀))).1.comp
        (hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (i₀ e₀)).injective)
  have hinj : Function.Injective (FundamentalGroup.map f (i₀ e₀)) := by
    change Function.Injective (FundamentalGroup.map
      ((hamiltonZeroAmbientMap phi).comp inclusion) (i₀ e₀))
    rw [FundamentalGroup.map_comp]
    exact hinjAmbient.comp hinjR
  exact boundary_groups_commensurable_of_contracted_arc i₀ i₁ f
    g₀ g₁ hg₀ hg₁ j hj h₀ h₁ e₀ e₁ k hinj F

end PoincareConjecture.M76
