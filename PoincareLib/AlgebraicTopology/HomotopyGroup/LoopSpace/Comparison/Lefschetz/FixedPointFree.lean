import Mathlib.Topology.Covering.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff

/-!
# Geometric separation for the compact deck calculation

Uniqueness of covering lifts makes a deck map fixing one point the identity.
A fixed-point-free continuous map on a compact Hausdorff space admits a
finite open cover in which each member is disjoint from its image. This
keeps the fixed-point hypothesis on the actual carrier, as required in the
Lefschetz argument of Hatcher, Theorem 2C.3, printed pp. 179-181, and the
compact-cover branch of MT Claim 18.16, p. 430.
-/

set_option autoImplicit false

open Set

universe u v

namespace IsCoveringMap

variable {E : Type u} {X : Type v} [TopologicalSpace E] [TopologicalSpace X]
  {p : E → X}

/-- A deck map fixing a point is the identity on a preconnected covering
space. Source: Hatcher, Proposition 1.34, printed p. 62. -/
theorem deck_eq_id_of_fixed [PreconnectedSpace E] (hp : IsCoveringMap p)
    (d : C(E, E)) (hd : p ∘ d = p) (x : E) (hx : d x = x) :
    d = ContinuousMap.id E := by
  apply ContinuousMap.ext
  exact congrFun (hp.eq_of_comp_eq d.continuous continuous_id hd x hx)

/-- Every nonidentity deck map on a preconnected covering space is
fixed-point-free. Source: Hatcher, Proposition 1.34, printed p. 62. -/
theorem deck_fixedPointFree_of_ne_id [PreconnectedSpace E] (hp : IsCoveringMap p)
    (d : C(E, E)) (hd : p ∘ d = p) (hne : d ≠ ContinuousMap.id E) :
    ∀ x, d x ≠ x :=
  fun x hx => hne (hp.deck_eq_id_of_fixed d hd x hx)

end IsCoveringMap

namespace ContinuousMap

/-- Each point of a fixed-point-free map has an open neighborhood disjoint
from its image. Source: Hatcher, Theorem 2C.3, printed pp. 179-181. -/
theorem exists_open_disjoint_image_of_fixedPointFree
    {X : Type u} [TopologicalSpace X] [T2Space X]
    (f : C(X, X)) (hfree : ∀ x, f x ≠ x) (x : X) :
    ∃ U : Set X, IsOpen U ∧ x ∈ U ∧ Disjoint U (f '' U) := by
  obtain ⟨U, V, hU, hV, hxU, hfxV, hUV⟩ := t2_separation (hfree x).symm
  refine ⟨U ∩ f ⁻¹' V, hU.inter (hV.preimage f.continuous), ⟨hxU, hfxV⟩, ?_⟩
  apply hUV.mono inter_subset_left
  rintro _ ⟨z, hz, rfl⟩
  exact hz.2

/-- A compact Hausdorff carrier has a finite open cover with each member
disjoint from its image under a fixed-point-free map.
Source: Hatcher, Theorem 2C.3, printed pp. 179-181. -/
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
