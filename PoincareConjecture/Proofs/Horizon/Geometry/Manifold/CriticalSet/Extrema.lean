import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Sublevel.Minimum
import Mathlib.Geometry.Manifold.Algebra.LieGroup

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Geometry.Manifold

theorem strict_bounds_on_interior_of_regular
    {n : Nat} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {h : M -> Real} (hh : ContMDiff (𝓡 n) 𝓘(Real, Real) ∞ h)
    {K : Set M} {p q : M} (hmin : IsMinOn h K p) (hmax : IsMaxOn h K q)
    (hreg : ∀ x ∈ K, mfderiv (𝓡 n) 𝓘(Real, Real) h x ≠ 0) :
    ∀ x ∈ interior K, h p < h x ∧ h x < h q := by
  intro x hx
  have hxK := interior_subset hx
  have hnhds := mem_interior_iff_mem_nhds.mp hx
  constructor
  · apply lt_of_le_of_ne (hmin hxK)
    intro heq
    have hxMin : IsMinOn h K x := by intro y hy; rw [← heq]; exact hmin hy
    exact hreg x hxK (mfderiv_eq_zero_of_isLocalMin hh (hxMin.isLocalMin hnhds))
  · apply lt_of_le_of_ne (hmax hxK)
    intro heq
    have hxMax : IsMaxOn h K x := by intro y hy; rw [heq]; exact hmax hy
    have hn := mfderiv_eq_zero_of_isLocalMin hh.neg (hxMax.isLocalMax hnhds).neg
    change mfderiv (𝓡 n) 𝓘(Real, Real) (-h) x = 0 at hn
    exact hreg x hxK (by simpa only [mfderiv_neg, neg_eq_zero] using hn)

theorem exists_boundary_extrema_of_regular
    {n : Nat} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {h : M -> Real} (hh : ContMDiff (𝓡 n) 𝓘(Real, Real) ∞ h)
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (hreg : ∀ p ∈ K, mfderiv (𝓡 n) 𝓘(Real, Real) h p ≠ 0) :
    ∃ p ∈ frontier K, ∃ q ∈ frontier K, IsMinOn h K p ∧ IsMaxOn h K q := by
  obtain ⟨p, hp, hmin⟩ := hK.exists_isMinOn hne hh.continuous.continuousOn
  obtain ⟨q, hq, hmax⟩ := hK.exists_isMaxOn hne hh.continuous.continuousOn
  refine ⟨p, ⟨subset_closure hp, ?_⟩, q, ⟨subset_closure hq, ?_⟩, hmin, hmax⟩
  · intro hpi
    exact hreg p hp (mfderiv_eq_zero_of_isLocalMin hh
      (hmin.isLocalMin (mem_interior_iff_mem_nhds.mp hpi)))
  · intro hqi
    have hn := mfderiv_eq_zero_of_isLocalMin hh.neg
      (hmax.isLocalMax (mem_interior_iff_mem_nhds.mp hqi)).neg
    change mfderiv (𝓡 n) 𝓘(Real, Real) (-h) q = 0 at hn
    exact hreg q hq (by simpa only [mfderiv_neg, neg_eq_zero] using hn)

theorem exists_two_distinct_critical_points
    {n : Nat} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace Real (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [CompactSpace M] [Nontrivial M]
    {h : M -> Real} (hh : ContMDiff (𝓡 n) 𝓘(Real, Real) ∞ h) :
    ∃ p q : M, p ≠ q ∧ mfderiv (𝓡 n) 𝓘(Real, Real) h p = 0 ∧
      mfderiv (𝓡 n) 𝓘(Real, Real) h q = 0 := by
  obtain ⟨p, _, hmin⟩ := isCompact_univ.exists_isMinOn univ_nonempty hh.continuous.continuousOn
  obtain ⟨q, _, hmax⟩ := isCompact_univ.exists_isMaxOn univ_nonempty hh.continuous.continuousOn
  have hp := mfderiv_eq_zero_of_isLocalMin hh (hmin.isLocalMin univ_mem)
  have hq : mfderiv (𝓡 n) 𝓘(Real, Real) h q = 0 := by
    have hneg := mfderiv_eq_zero_of_isLocalMin hh.neg (hmax.isLocalMax univ_mem).neg
    change mfderiv (𝓡 n) 𝓘(Real, Real) (-h) q = 0 at hneg
    simpa only [mfderiv_neg, neg_eq_zero] using hneg
  by_cases hpq : p = q
  · have hconstant : h = fun _ => h p := by
      funext x
      exact (hpq ▸ hmax (mem_univ x)).antisymm (hmin (mem_univ x))
    obtain ⟨x, y, hxy⟩ := exists_pair_ne M
    refine ⟨x, y, hxy, ?_, ?_⟩ <;> rw [hconstant] <;> exact mfderiv_const
  · exact ⟨p, q, hpq, hp, hq⟩

end Poincare.Geometry.Manifold
