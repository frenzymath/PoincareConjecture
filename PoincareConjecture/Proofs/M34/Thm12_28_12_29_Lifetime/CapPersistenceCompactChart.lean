import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactEnergy










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]




theorem capPersistence_exists_compact_chart_bounds (g : RiemannianMetric n M)
    (a : M) {H : Set (EuclideanSpace ℝ (Fin n))} (hH : IsCompact H)
    (hHt : H ⊆ (extChartAt (𝓡 n) a).target) (m : ℕ) :
    ∃ b : ℝ, 0 < b ∧ ∃ K : ℝ, 1 ≤ K ∧ ∀ y ∈ H,
      ‖y‖ ≤ K ∧
      (∀ j ≤ m, ‖iteratedFDeriv ℝ j
        (g.pullbackCoefficients (extChartAt (𝓡 n) a).symm) y‖ ≤ K) ∧
      (∀ v : EuclideanSpace ℝ (Fin n), b * ‖v‖ ^ 2 ≤
        g.pullbackCoefficients (extChartAt (𝓡 n) a).symm y v v) := by
  classical
  let c := extChartAt (𝓡 n) a
  let B := g.pullbackCoefficients c.symm
  have hs : ContDiffOn ℝ ∞ B c.target := g.contDiffOn_chartCoefficients a
  have hpos (y : EuclideanSpace ℝ (Fin n)) (hy : y ∈ H)
      (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) : 0 < B y v v := by
    have hi : (mfderiv (𝓡 n) (𝓡 n) c.symm y).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hHt hy)
    apply g.pos
    intro hz
    apply hv
    apply hi.injective
    rw [map_zero]
    convert! hz using 1
  obtain ⟨b, hb, hlow⟩ := exists_uniform_bilinear_lower_bound hH
    (hs.continuousOn.mono hHt) hpos
  obtain ⟨K0, hK0⟩ := hH.exists_bound_of_continuousOn continuousOn_id
  have hfinite (j : Fin (m + 1)) : ∃ C : ℝ,
      ∀ y ∈ H, ‖iteratedFDeriv ℝ (j : ℕ) B y‖ ≤ C :=
    hH.exists_bound_of_continuousOn
      ((ContinuousOn.continuousOn_iteratedFDeriv hs (isOpen_extChartAt_target a)
        (by exact_mod_cast le_top)).mono hHt)
  choose K hK using hfinite
  obtain ⟨K1, hK1⟩ := Finite.exists_le K
  refine ⟨b, hb, max 1 (max K0 K1), le_max_left _ _, ?_⟩
  intro y hy
  refine ⟨(hK0 y hy).trans ((le_max_left _ _).trans (le_max_right _ _)), ?_,
    hlow y hy⟩
  intro j hj
  exact ((hK ⟨j, by omega⟩ y hy).trans (hK1 ⟨j, by omega⟩)).trans
    ((le_max_right _ _).trans (le_max_right _ _))

end PoincareConjecture.RiemannianMetric
