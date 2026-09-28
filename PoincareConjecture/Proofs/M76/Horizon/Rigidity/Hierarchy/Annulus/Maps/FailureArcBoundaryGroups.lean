import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Coverings.Mathlib.FiniteFiberGroups
import PoincareConjecture.Proofs.Horizon.AlgebraicTopology.FundamentalGroup.PathMaps
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Hierarchy.Annulus.Maps.SecondPhaseGroups
import Mathlib.GroupTheory.Commensurable

set_option autoImplicit false
open Set

namespace IsCoveringMap

set_option backward.isDefEq.respectTransparency.types false in
theorem fundamentalGroup_range_finiteIndex_of_finite_fiber
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    {p : E → X} (hp : IsCoveringMap p) (e : E)
    [Finite (p ⁻¹' {p e})] :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.FiniteIndex := by
  classical
  let rho := hp.monodromyPerm (p e)
  have hker : rho.ker ≤ (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range := by
    intro gamma hgamma
    have hfix : hp.monodromy gamma ⟨e, rfl⟩ = ⟨e, rfl⟩ := by
      exact congrArg (fun f : Equiv.Perm (p ⁻¹' {p e}) => f ⟨e, rfl⟩) hgamma
    let delta : FundamentalGroup E e :=
      (hp.liftPathQuotient gamma ⟨e, rfl⟩).cast rfl (congrArg Subtype.val hfix).symm
    refine ⟨delta, ?_⟩
    change Path.Homotopic.Quotient.map delta ⟨p, hp.continuous⟩ = gamma
    simp only [delta, Path.Homotopic.Quotient.map_cast, hp.map_liftPathQuotient,
      Path.Homotopic.Quotient.cast_cast, Path.Homotopic.Quotient.cast_rfl_rfl]
  exact Subgroup.finiteIndex_of_le hker

theorem fundamentalGroup_range_finiteIndex_of_compact
    {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
    [CompactSpace E] [T1Space X]
    {p : E → X} (hp : IsCoveringMap p) (e : E) :
    (FundamentalGroup.map ⟨p, hp.continuous⟩ e).range.FiniteIndex := by
  let : CompactSpace (p ⁻¹' {p e}) :=
    isCompact_iff_compactSpace.mp (isClosed_singleton.preimage hp.continuous).isCompact
  let : DiscreteTopology (p ⁻¹' {p e}) := (hp (p e)).discreteTopology_fiber
  let : Finite (p ⁻¹' {p e}) := finite_of_compact_of_discrete
  exact hp.fundamentalGroup_range_finiteIndex_of_finite_fiber e

end IsCoveringMap

namespace PoincareConjecture.M76

private theorem commensurable_maps_of_finiteIndex
    {G H : Type*} [Group G] [Group H] (f : G →* H)
    (A B : Subgroup G) [A.FiniteIndex] [B.FiniteIndex] :
    (A.map f).Commensurable (B.map f) := by
  have : (A ⊔ f.ker).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  have : (B ⊔ f.ker).FiniteIndex := Subgroup.finiteIndex_of_le le_sup_left
  constructor
  · rw [Subgroup.relIndex_map_map]
    exact (Subgroup.isFiniteRelIndex_of_finiteIndex (H := A ⊔ f.ker)
      (K := B ⊔ f.ker)).relIndex_ne_zero
  · rw [Subgroup.relIndex_map_map]
    exact (Subgroup.isFiniteRelIndex_of_finiteIndex (H := B ⊔ f.ker)
      (K := A ⊔ f.ker)).relIndex_ne_zero

private theorem transport_back_apply
    {X : Type*} [TopologicalSpace X] {x y : X} (k : Path x y)
    (gamma : FundamentalGroup X y) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm gamma =
      (Path.Homotopic.Quotient.mk k).trans
        (gamma.trans (Path.Homotopic.Quotient.mk k).symm) := by
  change (Path.Homotopic.Quotient.mk k.symm.symm).trans
    (gamma.trans (Path.Homotopic.Quotient.mk k.symm)) = _
  rw [Path.symm_symm]
  rfl

private theorem conjugate_cast_refl
    {Y : Type*} [TopologicalSpace Y] {a b : Y} (h : b = a)
    (gamma : Path.Homotopic.Quotient b b) :
    ((Path.Homotopic.Quotient.refl a).cast rfl h).trans
      (gamma.trans ((Path.Homotopic.Quotient.refl a).cast rfl h).symm) =
        gamma.cast h.symm h.symm := by
  subst b
  simp only [Path.Homotopic.Quotient.cast_rfl_rfl]
  change (Path.Homotopic.Quotient.refl a).trans
    (gamma.trans (Path.Homotopic.Quotient.refl a)) = gamma
  simp only [Path.Homotopic.Quotient.refl_trans, Path.Homotopic.Quotient.trans_refl]

theorem fundamentalGroup_map_transport_of_contracted_path
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {x y : X} (k : Path x y)
    (F : (f.comp k.toContinuousMap).HomotopyRel
      (ContinuousMap.const unitInterval (f x)) ({0, 1} : Set unitInterval)) :
    ∃ h : f y = f x,
      (FundamentalGroup.map f x).comp
          (FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom =
        FundamentalGroup.mapOfEq f h := by
  have h : f y = f x := by
    have hh := F.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl)
    change f (k 1) = f x at hh
    simpa only [Path.target] using hh
  refine ⟨h, ?_⟩
  have hclass : (Path.Homotopic.Quotient.mk k).map f =
      (Path.Homotopic.Quotient.refl (f x)).cast rfl h := by
    exact Quotient.sound ⟨F⟩
  ext gamma
  change Path.Homotopic.Quotient.map
    (FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm gamma) f = _
  rw [transport_back_apply, Path.Homotopic.Quotient.map_trans,
    Path.Homotopic.Quotient.map_trans, Path.Homotopic.Quotient.map_symm, hclass,
    FundamentalGroup.mapOfEq_apply]
  exact conjugate_cast_refl h _

private theorem mapOfEq_rfl
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (x : X) :
    FundamentalGroup.mapOfEq f (rfl : f x = f x) = FundamentalGroup.map f x := by
  ext gamma
  rw [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.cast_rfl_rfl]
  rfl

private theorem mapOfEq_comp
    {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(X, Y)) (g : C(Y, Z)) {x : X} {y : Y} {z : Z}
    (hf : f x = y) (hg : g y = z) :
    (FundamentalGroup.mapOfEq g hg).comp (FundamentalGroup.mapOfEq f hf) =
      FundamentalGroup.mapOfEq (g.comp f) ((congrArg g hf).trans hg) := by
  subst y
  subst z
  simp only [mapOfEq_rfl]
  exact (FundamentalGroup.map_comp f g x).symm

private theorem mapOfEq_finiteIndex_of_compact_covering
    {E T : Type*} [TopologicalSpace E] [TopologicalSpace T]
    [CompactSpace E] [T1Space T] (g : C(E, T)) (hg : IsCoveringMap g)
    {e : E} {t : T} (he : g e = t) :
    (FundamentalGroup.mapOfEq g he).range.FiniteIndex := by
  subst t
  rw [mapOfEq_rfl]
  exact hg.fundamentalGroup_range_finiteIndex_of_compact e

private theorem mapOfEq_congr
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f g : C(X, Y)} (hfg : f = g) {x : X} {y : Y}
    (hf : f x = y) (hg : g x = y) :
    FundamentalGroup.mapOfEq f hf = FundamentalGroup.mapOfEq g hg := by
  subst g
  rfl

theorem boundary_groups_commensurable_of_contracted_arc
    {E₀ E₁ X T Y : Type*}
    [TopologicalSpace E₀] [TopologicalSpace E₁] [TopologicalSpace X]
    [TopologicalSpace T] [TopologicalSpace Y]
    [CompactSpace E₀] [CompactSpace E₁] [T1Space T]
    (i₀ : C(E₀, X)) (i₁ : C(E₁, X)) (f : C(X, Y))
    (g₀ : C(E₀, T)) (g₁ : C(E₁, T))
    (hg₀ : IsCoveringMap g₀) (hg₁ : IsCoveringMap g₁)
    (j : C(T, Y)) (hj : Function.Injective j)
    (h₀ : f.comp i₀ = j.comp g₀) (h₁ : f.comp i₁ = j.comp g₁)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (hinj : Function.Injective (FundamentalGroup.map f (i₀ e₀)))
    (F : (f.comp k.toContinuousMap).HomotopyRel
      (ContinuousMap.const unitInterval (f (i₀ e₀))) ({0, 1} : Set unitInterval)) :
    (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range := by
  obtain ⟨hbase, htransport⟩ := fundamentalGroup_map_transport_of_contracted_path f k F
  have hbase₀ : f (i₀ e₀) = j (g₀ e₀) := DFunLike.congr_fun h₀ e₀
  have hbase₁ : f (i₁ e₁) = j (g₁ e₁) := DFunLike.congr_fun h₁ e₁
  have htorus : g₁ e₁ = g₀ e₀ := hj (hbase₁.symm.trans (hbase.trans hbase₀))
  let a₀ := FundamentalGroup.map g₀ e₀
  let a₁ := FundamentalGroup.mapOfEq g₁ htorus
  let J := FundamentalGroup.mapOfEq j hbase₀.symm
  let b₀ := FundamentalGroup.map i₀ e₀
  let b₁ := (FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
    (FundamentalGroup.map i₁ e₁)
  let M := FundamentalGroup.map f (i₀ e₀)
  have ha₀ : a₀.range.FiniteIndex := hg₀.fundamentalGroup_range_finiteIndex_of_compact e₀
  have ha₁ : a₁.range.FiniteIndex := mapOfEq_finiteIndex_of_compact_covering g₁ hg₁ htorus
  have heq₀ : M.comp b₀ = J.comp a₀ := by
    change (FundamentalGroup.map f (i₀ e₀)).comp (FundamentalGroup.map i₀ e₀) = _
    rw [← FundamentalGroup.map_comp]
    change FundamentalGroup.map (f.comp i₀) e₀ =
      (FundamentalGroup.mapOfEq j hbase₀.symm).comp (FundamentalGroup.map g₀ e₀)
    rw [← mapOfEq_rfl g₀ e₀, mapOfEq_comp]
    rw [← mapOfEq_rfl (f.comp i₀) e₀]
    exact mapOfEq_congr h₀ _ _
  have heq₁ : M.comp b₁ = J.comp a₁ := by
    change (FundamentalGroup.map f (i₀ e₀)).comp
      ((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom.comp
        (FundamentalGroup.map i₁ e₁)) = _
    rw [← MonoidHom.comp_assoc, htransport]
    rw [← mapOfEq_rfl i₁ e₁, mapOfEq_comp]
    change FundamentalGroup.mapOfEq (f.comp i₁) _ =
      (FundamentalGroup.mapOfEq j hbase₀.symm).comp (FundamentalGroup.mapOfEq g₁ htorus)
    rw [mapOfEq_comp]
    exact mapOfEq_congr h₁ _ _
  have hcomm : (a₀.range.map J).Commensurable (a₁.range.map J) :=
    commensurable_maps_of_finiteIndex J a₀.range a₁.range
  have hmap₀ : b₀.range.map M = a₀.range.map J := by
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp, heq₀]
  have hmap₁ : b₁.range.map M = a₁.range.map J := by
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp, heq₁]
  rw [← hmap₀, ← hmap₁] at hcomm
  change b₀.range.Commensurable b₁.range
  constructor
  · rw [← Subgroup.relIndex_map_map_of_injective b₀.range b₁.range hinj]
    exact hcomm.1
  · rw [← Subgroup.relIndex_map_map_of_injective b₁.range b₀.range hinj]
    exact hcomm.2

local notation "L0" => hamiltonZeroPeriodLattice
local notation "X0" => LatticeHandleAmbient (Fin 0) (Fin 3) L0
local notation "H0" => LatticeHandle (Fin 0) (Fin 3) L0
local notation "B0" => latticeHandleBoundary (Fin 0) (Fin 3) L0
local notation "p" => (4 * (16 : ℝ))
local notation "C0" => AddCircle p
local notation "Q0" => hamiltonZeroAmbientEquiv.trans hamiltonZeroHierarchyCoordinates

theorem hamiltonZero_boundary_groups_commensurable_of_failure_arc
    {E₀ E₁ : Type*} [TopologicalSpace E₀] [TopologicalSpace E₁]
    [CompactSpace E₀] [CompactSpace E₁]
    (phi : C(H0, H0)) (F₀ : (ContinuousMap.id H0).HomotopyRel phi B0)
    (i₀ : C(E₀, X0)) (i₁ : C(E₁, X0))
    (g₀ : C(E₀, C0 × C0)) (g₁ : C(E₁, C0 × C0))
    (hg₀ : IsCoveringMap g₀) (hg₁ : IsCoveringMap g₁) (delta₀ delta₁ : C0)
    (htangent₀ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₀ z))).1 = g₀ z)
    (htangent₁ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₁ z))).1 = g₁ z)
    (hnormal₀ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₀ z))).2 = delta₀)
    (hnormal₁ : ∀ z, (Q0 (hamiltonZeroAmbientMap phi (i₁ z))).2 = delta₁)
    (e₀ : E₀) (e₁ : E₁) (k : Path (i₀ e₀) (i₁ e₁))
    (F : ((hamiltonZeroAmbientMap phi).comp k.toContinuousMap).HomotopyRel
      (ContinuousMap.const unitInterval (hamiltonZeroAmbientMap phi (i₀ e₀)))
      ({0, 1} : Set unitInterval)) :
    delta₀ = delta₁ ∧ (FundamentalGroup.map i₀ e₀).range.Commensurable
      (((FundamentalGroup.fundamentalGroupMulEquivOfPath k.symm).toMonoidHom).comp
        (FundamentalGroup.map i₁ e₁)).range := by
  let : Fact (0 < p) := ⟨by norm_num⟩
  have hends : hamiltonZeroAmbientMap phi (i₁ e₁) = hamiltonZeroAmbientMap phi (i₀ e₀) := by
    have hh := F.fst_eq_snd (show (1 : unitInterval) ∈ ({0, 1} : Set unitInterval) from Or.inr rfl)
    change hamiltonZeroAmbientMap phi (k 1) = hamiltonZeroAmbientMap phi (i₀ e₀) at hh
    simpa only [Path.target] using hh
  have hlabels : delta₁ = delta₀ := (hnormal₁ e₁).symm.trans
    ((congrArg (fun z => (Q0 z).2) hends).trans (hnormal₀ e₀))
  refine ⟨hlabels.symm, ?_⟩
  subst delta₁
  let j : C(C0 × C0, X0) := ⟨fun z => (Q0).symm (z, delta₀), by fun_prop⟩
  have hj : Function.Injective j := by
    intro x y hxy
    exact congrArg Prod.fst ((Q0).symm.injective hxy)
  have h₀ : (hamiltonZeroAmbientMap phi).comp i₀ = j.comp g₀ := by
    apply ContinuousMap.ext
    intro z
    apply (Q0).injective
    change Q0 (hamiltonZeroAmbientMap phi (i₀ z)) = Q0 ((Q0).symm (g₀ z, delta₀))
    rw [(Q0).apply_symm_apply]
    exact Prod.ext (htangent₀ z) (hnormal₀ z)
  have h₁ : (hamiltonZeroAmbientMap phi).comp i₁ = j.comp g₁ := by
    apply ContinuousMap.ext
    intro z
    apply (Q0).injective
    change Q0 (hamiltonZeroAmbientMap phi (i₁ z)) = Q0 ((Q0).symm (g₁ z, delta₀))
    rw [(Q0).apply_symm_apply]
    exact Prod.ext (htangent₁ z) (hnormal₁ z)
  let ambient : C(X0, H0) := hamiltonZeroAmbientEquiv
  let inverse : C(H0, X0) := hamiltonZeroAmbientEquiv.symm
  have hinj : Function.Injective (FundamentalGroup.map (hamiltonZeroAmbientMap phi) (i₀ e₀)) := by
    change Function.Injective (FundamentalGroup.map (inverse.comp (phi.comp ambient)) (i₀ e₀))
    rw [FundamentalGroup.map_comp, FundamentalGroup.map_comp]
    exact (hamiltonZeroAmbientEquiv.symm.fundamentalGroupMulEquiv
      (phi (ambient (i₀ e₀)))).injective.comp
      ((F₀.fundamentalGroup_map_bijective (ambient (i₀ e₀))).1.comp
        (hamiltonZeroAmbientEquiv.fundamentalGroupMulEquiv (i₀ e₀)).injective)
  exact boundary_groups_commensurable_of_contracted_arc i₀ i₁ (hamiltonZeroAmbientMap phi)
    g₀ g₁ hg₀ hg₁ j hj h₀ h₁ e₀ e₁ k hinj F

end PoincareConjecture.M76
