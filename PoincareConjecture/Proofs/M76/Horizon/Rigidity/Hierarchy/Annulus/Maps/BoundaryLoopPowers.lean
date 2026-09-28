import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.FailureArcRegionGroups








set_option autoImplicit false

namespace PoincareConjecture.M76

noncomputable def boundaryLoopIterate {X : Type*} [TopologicalSpace X] {x : X}
    (alpha : Path x x) : ℕ → Path x x
  | 0 => Path.refl x
  | n + 1 => alpha.trans (boundaryLoopIterate alpha n)

theorem boundaryLoopIterate_class {X : Type*} [TopologicalSpace X] {x : X}
    (alpha : Path x x) (n : ℕ) :
    let a : FundamentalGroup X x := Path.Homotopic.Quotient.mk alpha
    a ^ n = Path.Homotopic.Quotient.mk (boundaryLoopIterate alpha n) := by
  dsimp only
  induction n with
  | zero => rfl
  | succ n hn =>
    rw [boundaryLoopIterate, Path.Homotopic.Quotient.mk_trans, pow_succ, hn]
    rfl

theorem exists_boundary_loop_power_homotopy
    {E₀ E₁ R : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [TopologicalSpace R]
    (i₀ : C(E₀, R)) (i₁ : C(E₁, R)) (x₀ : E₀) (x₁ : E₁)
    (k : Path (i₀ x₀) (i₁ x₁))
    (hc : (FundamentalGroup.map i₀ x₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ x₁)).range)
    (alpha : Path x₀ x₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ beta : Path x₁ x₁,
      ((boundaryLoopIterate alpha n).map i₀.continuous).Homotopic
        (k.trans ((beta.map i₁.continuous).trans k.symm)) := by
  let a : FundamentalGroup E₀ x₀ := Path.Homotopic.Quotient.mk alpha
  let f := FundamentalGroup.map i₀ x₀
  let g := ((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
    (FundamentalGroup.map i₁ x₁)
  obtain ⟨n, hn, _, hnmem⟩ :=
    Subgroup.exists_pow_mem_of_relIndex_ne_zero hc.2 (show f a ∈ f.range from ⟨a, rfl⟩)
  obtain ⟨b, hb⟩ := hnmem.1
  obtain ⟨beta, hbeta⟩ := Path.Homotopic.Quotient.mk_surjective b
  refine ⟨n, hn, beta, Path.Homotopic.Quotient.exact ?_⟩
  have hclass : f (a ^ n) = g (Path.Homotopic.Quotient.mk beta) := by
    rw [hbeta, map_pow]
    exact hb.symm
  rw [Path.Homotopic.Quotient.mk_map, ← boundaryLoopIterate_class]
  change f (a ^ n) = _
  rw [hclass, Path.Homotopic.Quotient.mk_trans, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_symm]
  change (Path.Homotopic.Quotient.mk k.symm.symm).trans
    ((Path.Homotopic.Quotient.map (Path.Homotopic.Quotient.mk beta) i₁).trans
      (Path.Homotopic.Quotient.mk k.symm)) = _
  rw [Path.symm_symm, Path.Homotopic.Quotient.mk_symm]


local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "C0" => AddCircle (4 * (16 : ℝ))
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_boundary_loop_power_homotopy_of_failure_arc
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
      ({0, 1} : Set unitInterval))
    (alpha : Path e₀ e₀) :
    ∃ n : ℕ, 0 < n ∧ ∃ beta : Path e₁ e₁,
      ((boundaryLoopIterate alpha n).map i₀.continuous).Homotopic
        (k.trans ((beta.map i₁.continuous).trans k.symm)) := by
  have hc := (hamiltonZero_region_boundary_groups_commensurable_of_failure_arc
    phi F₀ R i₀ i₁ g₀ g₁ hg₀ hg₁ delta₀ delta₁ htangent₀ htangent₁
    hnormal₀ hnormal₁ e₀ e₁ k hinjR F).2
  exact exists_boundary_loop_power_homotopy i₀ i₁ e₀ e₁ k hc alpha

end PoincareConjecture.M76
