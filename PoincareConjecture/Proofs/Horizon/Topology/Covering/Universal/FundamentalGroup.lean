




module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected



































public section

open CategoryTheory

namespace FundamentalGroupoid



theorem nonempty_hom {Y : Type*} [TopologicalSpace Y]
    [PathConnectedSpace Y] (x y : FundamentalGroupoid Y) : Nonempty (x ⟶ y) :=
  ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath x.as y.as)⟩

end FundamentalGroupoid

namespace Poincare.Topology

variable {E X : Type*} [TopologicalSpace E] [TopologicalSpace X]
variable {A : Type*} [TopologicalSpace A]


theorem FundamentalGroup.map_fromPath {Y : Type*} [TopologicalSpace Y] (f : C(X, Y)) (base : X)
    (q : Path base base) :
    _root_.FundamentalGroup.map f base (_root_.FundamentalGroup.fromPath ⟦q⟧) =
      _root_.FundamentalGroup.fromPath ⟦q.map f.continuous⟧ := by
  rfl




theorem FundamentalGroup.map_range_eq_bot_iff {Y : Type*} [TopologicalSpace Y] (f : C(X, Y))
    (base : X) :
    (_root_.FundamentalGroup.map f base).range = ⊥ ↔
      ∀ γ : Path base base, (γ.map f.continuous).Homotopic (Path.refl (f base)) := by
  rw [MonoidHom.range_eq_bot_iff]
  constructor
  · intro h γ
    have h_map : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ := by
      rw [← FundamentalGroup.map_fromPath f base γ, h]

      exact FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (f base))
    exact (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mp h_map
  · intro h
    ext p
    obtain ⟨γ, rfl⟩ := Quotient.exists_rep (_root_.FundamentalGroup.toPath p)
    have hnull : _root_.FundamentalGroup.fromPath ⟦γ.map f.continuous⟧ =
        _root_.FundamentalGroup.fromPath ⟦Path.refl (f base)⟧ :=
      (FundamentalGroupoid.fromPath_eq_iff_homotopic _ _).mpr (h γ)
    rw [FundamentalGroup.map_fromPath f base γ, hnull]
    exact (FundamentalGroupoid.id_eq_path_refl (FundamentalGroupoid.mk (f base))).symm



@[simp]
theorem FundamentalGroup.map_range_eq_bot_of_subsingleton
    {a₀ : A} [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) :
    (_root_.FundamentalGroup.map f a₀).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.map f a₀).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.map f a₀).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _


theorem FundamentalGroup.map_range_eq_bot_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) : (_root_.FundamentalGroup.map f a₀).range = ⊥ :=
  FundamentalGroup.map_range_eq_bot_of_subsingleton f



theorem FundamentalGroup.map_range_le_of_subsingleton
    {a₀ : A} [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X))
    (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H := by
  rw [FundamentalGroup.map_range_eq_bot_of_subsingleton f]
  exact bot_le



@[simp]
theorem FundamentalGroup.mapOfEq_range_eq_bot_of_subsingleton
    {a₀ : A} [Subsingleton (_root_.FundamentalGroup A a₀)] (f : C(A, X)) {x : X} (h : f a₀ = x) :
    (_root_.FundamentalGroup.mapOfEq f h).range = ⊥ := by
  have : Subsingleton ((_root_.FundamentalGroup.mapOfEq f h).range) :=
    (Set.subsingleton_coe _).mpr ((_root_.FundamentalGroup.mapOfEq f h).subsingleton_coe_range)
  exact Subgroup.eq_bot_of_subsingleton _



theorem FundamentalGroup.map_range_le_of_simplyConnectedSpace [SimplyConnectedSpace A]
    (f : C(A, X)) (a₀ : A) (H : Subgroup (_root_.FundamentalGroup X (f a₀))) :
    (_root_.FundamentalGroup.map f a₀).range ≤ H :=
  FundamentalGroup.map_range_le_of_subsingleton f H

end Poincare.Topology
