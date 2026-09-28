import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

set_option autoImplicit false

open Set

universe u v

namespace IsCoveringMap

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X}

theorem deck_eq_id_of_fixed [PreconnectedSpace E] (hp : IsCoveringMap p)
    (d : C(E, E)) (hd : p ∘ d = p) (x : E) (hx : d x = x) :
    d = ContinuousMap.id E := by
  apply ContinuousMap.ext
  exact congrFun (hp.eq_of_comp_eq d.continuous continuous_id hd x hx)

theorem deck_fixedPointFree_of_ne_id [PreconnectedSpace E] (hp : IsCoveringMap p)
    (d : C(E, E)) (hd : p ∘ d = p) (hne : d ≠ ContinuousMap.id E) :
    ∀ x, d x ≠ x :=
  fun x hx => hne (hp.deck_eq_id_of_fixed d hd x hx)

end IsCoveringMap

namespace ContinuousMap

theorem exists_open_disjoint_image_of_fixedPointFree
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (f : C(X, X)) (hfree : ∀ x, f x ≠ x) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Disjoint U (f '' U) := by
  obtain ⟨U, V, hU, hV, hxU, hfxV, hUV⟩ := t2_separation (hfree x).symm
  refine ⟨U ∩ f ⁻¹' V, hU.inter (hV.preimage f.continuous), ⟨hxU, hfxV⟩, ?_⟩
  apply hUV.mono inter_subset_left
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

theorem exists_finite_open_cover_disjoint_image_of_fixedPointFree
    {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    (f : C(X, X)) (hfree : ∀ x, f x ≠ x) :
    ∃ (S : Finset X) (U : X → Set X),
      (∀ x, IsOpen (U x)) ∧ (∀ x, Disjoint (U x) (f '' U x)) ∧
        (univ : Set X) ⊆ ⋃ x ∈ S, U x := by
  classical
  choose U hU hxU hdis using f.exists_open_disjoint_image_of_fixedPointFree hfree
  obtain ⟨S, hS⟩ := isCompact_univ.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hxU x⟩)
  exact ⟨S, U, hU, hdis, hS⟩

end ContinuousMap
