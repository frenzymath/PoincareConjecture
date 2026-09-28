module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import Mathlib.Topology.Homotopy.LocallyContractible
public import Mathlib.Topology.Homotopy.Product

import PoincareConjecture.Proofs.Horizon.Topology.Covering.Universal.PathHomotopy

public section

open Topology

namespace Poincare.Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

class SemilocallySimplyConnectedSpace (X : Type*) [TopologicalSpace X] : Prop where

  exists_mem_nhds_loops_nullhomotopic (x : X) :
    ∃ U ∈ 𝓝 x, ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x)

namespace SemilocallySimplyConnectedSpace

variable [SemilocallySimplyConnectedSpace X]

theorem exists_mem_nhds_subset_loops_nullhomotopic (x : X) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U ∈ 𝓝 x, U ⊆ V ∧ ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hloop⟩ := exists_mem_nhds_loops_nullhomotopic (X := X) x
  refine ⟨U ∩ V, Filter.inter_mem hU hV, Set.inter_subset_right, fun γ hγ => ?_⟩
  exact hloop γ fun t => (hγ t).1

theorem exists_isOpen_mem_nhds_subset_loops_nullhomotopic (x : X) {V : Set X} (hV : V ∈ 𝓝 x) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ U ⊆ V ∧
      ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hU, hUV, hloop⟩ := exists_mem_nhds_subset_loops_nullhomotopic x hV
  obtain ⟨W, hWU, hWopen, hxW⟩ := mem_nhds_iff.mp hU
  exact ⟨W, hWopen, hxW, hWU.trans hUV, fun γ hγ => hloop γ fun t => hWU (hγ t)⟩

theorem exists_isOpen_mem_nhds_loops_nullhomotopic (x : X) :
    ∃ U, IsOpen U ∧ x ∈ U ∧ ∀ γ : Path x x, (∀ t, γ t ∈ U) → γ.Homotopic (Path.refl x) := by
  obtain ⟨U, hUopen, hxU, -, hloop⟩ :=
    exists_isOpen_mem_nhds_subset_loops_nullhomotopic x (V := Set.univ) Filter.univ_mem
  exact ⟨U, hUopen, hxU, hloop⟩

end SemilocallySimplyConnectedSpace

theorem SemilocallySimplyConnectedSpace.of_forall_exists_mem_nhds_isSimplyConnected
    (h : ∀ x : X, ∃ U ∈ 𝓝 x, IsSimplyConnected U) : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    obtain ⟨U, hU, hsc⟩ := h x
    refine ⟨U, hU, fun γ hγ => ?_⟩
    obtain ⟨F, -⟩ :=
      (isSimplyConnected_iff_exists_homotopy_refl_forall_mem.mp hsc).2 x γ hγ
    exact ⟨F⟩

theorem SemilocallySimplyConnectedSpace.of_locallyContractibleSpace
    (h : LocallyContractibleSpace X) : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    obtain ⟨V, hVU, hV, hnull⟩ := h x Set.univ Filter.univ_mem

    let j : C(V, X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hnj : j.Nullhomotopic :=
      hnull.comp_right (⟨Subtype.val, continuous_subtype_val⟩ : C((Set.univ : Set X), X))
    refine ⟨V, hV, fun γ hγ => ?_⟩
    exact Path.Homotopic.refl_of_forall_mem_of_nullhomotopic hnj γ hγ

instance (priority := 100) [SimplyConnectedSpace X] : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x :=
    ⟨Set.univ, Filter.univ_mem,
      fun γ _ => (simply_connected_iff_loops_nullhomotopic.mp ‹_›).2 x γ⟩

instance (priority := 100) [StronglyLocallyContractibleSpace X] :
    SemilocallySimplyConnectedSpace X :=
  .of_locallyContractibleSpace StronglyLocallyContractibleSpace.locallyContractible

instance (priority := 100) [DiscreteTopology X] : SemilocallySimplyConnectedSpace X where
  exists_mem_nhds_loops_nullhomotopic x := by
    refine ⟨{x}, (isOpen_discrete _).mem_nhds rfl, fun γ hγ => ?_⟩
    have hγx : γ = Path.refl x := by
      ext t
      simpa using hγ t
    rw [hγx]

instance [SemilocallySimplyConnectedSpace X] [SemilocallySimplyConnectedSpace Y] :
    SemilocallySimplyConnectedSpace (X × Y) where
  exists_mem_nhds_loops_nullhomotopic := by
    rintro ⟨x, y⟩
    obtain ⟨U, hU, hUloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (X := X) x
    obtain ⟨V, hV, hVloop⟩ :=
      SemilocallySimplyConnectedSpace.exists_mem_nhds_loops_nullhomotopic (X := Y) y
    refine ⟨U ×ˢ V, prod_mem_nhds hU hV, fun γ hγ => ?_⟩
    obtain ⟨F₁⟩ := hUloop (γ.map continuous_fst) fun t => (Set.mem_prod.mp (hγ t)).1
    obtain ⟨F₂⟩ := hVloop (γ.map continuous_snd) fun t => (Set.mem_prod.mp (hγ t)).2
    have key : ((γ.map continuous_fst).prod (γ.map continuous_snd)).Homotopic
        ((Path.refl x).prod (Path.refl y)) := ⟨Path.Homotopic.prodHomotopy F₁ F₂⟩
    have hleft : (γ.map continuous_fst).prod (γ.map continuous_snd) = γ := by
      ext t <;> simp
    have hright : (Path.refl x).prod (Path.refl y) = Path.refl (x, y) := by
      ext t <;> simp
    rwa [hleft, hright] at key

end Poincare.Topology
