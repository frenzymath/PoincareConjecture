import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset








set_option autoImplicit false

open Set Filter
open scoped Topology

namespace Poincare.Analysis

theorem eventually_uniform_abs_bound_on_compact_of_local_oscillation
    {X : Type*} [TopologicalSpace X] [PreconnectedSpace X]
    (f : ℕ → X → ℝ)
    (hosc : ∀ x : X, ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ y ∈ U, ∀ z ∈ U, |f k y - f k z| ≤ C)
    {p : X} (hp : ∃ C : ℝ, ∀ᶠ k in atTop, |f k p| ≤ C)
    {K : Set X} (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ k in atTop, ∀ x ∈ K, |f k x| ≤ C := by
  classical
  let B : Set X := {x | ∃ C : ℝ, ∀ᶠ k in atTop, |f k x| ≤ C}
  have transfer {U : Set X} {D : ℝ}
      (hD : ∀ᶠ k in atTop, ∀ y ∈ U, ∀ z ∈ U, |f k y - f k z| ≤ D)
      {x y : X} (hx : x ∈ U) (hy : y ∈ U) (hbx : x ∈ B) : y ∈ B := by
    obtain ⟨C, hC⟩ := hbx
    refine ⟨D + C, ?_⟩
    filter_upwards [hD, hC] with k hk hck
    calc
      |f k y| = |(f k y - f k x) + f k x| := by congr 1; ring
      _ ≤ |f k y - f k x| + |f k x| := abs_add_le _ _
      _ ≤ D + C := add_le_add (hk y hy x hx) hck
  have hBo : IsOpen B := by
    rw [isOpen_iff_forall_mem_open]
    intro x hbx
    obtain ⟨U, hU, hx, D, hD⟩ := hosc x
    exact ⟨U, fun y hy => transfer hD hx hy hbx, hU, hx⟩
  have hBc : IsClosed B := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro x hbx
    obtain ⟨U, hU, hx, D, hD⟩ := hosc x
    exact ⟨U, fun y hy hby => hbx (transfer hD hy hx hby), hU, hx⟩
  have hB : B = univ := (show IsClopen B from ⟨hBc, hBo⟩).eq_univ ⟨p, hp⟩
  have hlocal (x : X) : ∃ U : Set X, IsOpen U ∧ x ∈ U ∧
      ∃ C : ℝ, ∀ᶠ k in atTop, ∀ y ∈ U, |f k y| ≤ C := by
    obtain ⟨U, hU, hx, D, hD⟩ := hosc x
    obtain ⟨C, hC⟩ : x ∈ B := by rw [hB]; trivial
    refine ⟨U, hU, hx, D + C, ?_⟩
    filter_upwards [hD, hC] with k hk hck y hy
    calc
      |f k y| = |(f k y - f k x) + f k x| := by congr 1; ring
      _ ≤ |f k y - f k x| + |f k x| := abs_add_le _ _
      _ ≤ D + C := add_le_add (hk y hy x hx) hck
  choose U hU hx C hC using hlocal
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover U hU
    (fun x _ => mem_iUnion.mpr ⟨x, hx x⟩)
  refine ⟨∑ x ∈ t, max (C x) 0, Finset.sum_nonneg (fun _ _ => le_max_right _ _), ?_⟩
  have he := (Filter.eventually_all_finite t.finite_toSet).mpr (fun x _ => hC x)
  filter_upwards [he] with k hk x hxK
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (ht hxK)
  exact (hk y hy x hxy).trans ((le_max_left _ _).trans
    (Finset.single_le_sum (fun z _ => le_max_right (C z) 0) hy))

end Poincare.Analysis
