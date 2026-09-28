import Mathlib.Topology.Homeomorph.Lemmas
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

open Set Topology

namespace Topology.IsQuotientMap

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

theorem exists_regular_homeomorph {q : X → Y} (hq : IsQuotientMap q)
    {T : Set Y} (hT : IsOpen T) (hinj : InjOn q (q ⁻¹' T)) :
    ∃ R : (q ⁻¹' T) ≃ₜ T, ∀ x, (R x : Y) = q x := by
  let r := T.restrictPreimage q
  have hqr : IsQuotientMap r := hq.restrictPreimage_isOpen hT
  have hir : Function.Injective r := by
    intro x y h
    exact Subtype.ext (hinj x.property y.property (congrArg Subtype.val h))
  have hr : IsHomeomorph r := isHomeomorph_iff_isQuotientMap_injective.mpr ⟨hqr, hir⟩
  exact ⟨hr.homeomorph r, fun _ => rfl⟩

theorem isOpen_image_of_saturated {q : X → Y} (hq : IsQuotientMap q)
    {U : Set X} (hU : IsOpen U) (hsat : q ⁻¹' (q '' U) = U) :
    IsOpen (q '' U) := by
  apply hq.isOpen_preimage.mp
  rwa [hsat]

end Topology.IsQuotientMap

namespace ContinuousMap

variable {X Y : Type*} [TopologicalSpace X] [CompactSpace X]
  [TopologicalSpace Y] [T2Space Y]

theorem exists_two_fiber_regular_homeomorph (q : C(X, Y))
    (hq : Function.Surjective q) (a b : Y)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b)) :
    ∃ R : (q ⁻¹' ({a, b} : Set Y)ᶜ) ≃ₜ ↥(({a, b} : Set Y)ᶜ),
      ∀ x, (R x : Y) = q x := by
  apply (q.continuous.isClosedMap.isQuotientMap q.continuous hq).exists_regular_homeomorph
    ((Set.finite_singleton b).insert a).isClosed.isOpen_compl
  intro x hx y _ hxy
  rcases (hfib x y).mp hxy with h | h | h
  · exact h
  · exact False.elim (hx (by simp [h.1]))
  · exact False.elim (hx (by simp [h.1]))

theorem isOpen_image_of_contains_two_fibers (q : C(X, Y))
    (hq : Function.Surjective q) (a b : Y)
    (hfib : ∀ x y, q x = q y ↔ x = y ∨
      (q x = a ∧ q y = a) ∨ (q x = b ∧ q y = b))
    {U : Set X} (hU : IsOpen U) (ha : q ⁻¹' {a} ⊆ U) (hb : q ⁻¹' {b} ⊆ U) :
    IsOpen (q '' U) := by
  apply (q.continuous.isClosedMap.isQuotientMap q.continuous hq).isOpen_image_of_saturated hU
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    rcases (hfib x y).mp hxy.symm with h | h | h
    · exact h.symm ▸ hy
    · exact ha h.1
    · exact hb h.1
  · intro hx
    exact ⟨x, hx, rfl⟩

end ContinuousMap
