import PoincareLib.Geometry.Riemannian.Curvature.SectionalBounds
import PoincareLib.Geometry.RicciFlow.Basic

/-! # Vanishing full curvature in dimensions zero and one

Antisymmetry in the last curvature slots makes every orthonormal-frame
component vanish when the frame has at most one index. The full retained
curvature norm is therefore zero, uniformly in every represented flow time.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle BigOperators

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The full retained curvature norm vanishes in dimension at most one. -/
theorem LeviCivitaData.curvatureTensorNorm_eq_zero_of_dimension_le_one
    {g : RiemannianMetric n M} (D : LeviCivitaData g) (hn : n ≤ 1) (x : M) :
    D.curvatureTensorNorm x = 0 := by
  let b := g.orthonormalBasis x
  have hdim : Module.finrank ℝ (TangentSpace (𝓡 n) x) = n :=
    finrank_euclideanSpace_fin
  have hindex (k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) : k = l := by
    apply Fin.ext
    have hk := k.isLt
    have hl := l.isLt
    omega
  have hzero (i j k l : Fin (Module.finrank ℝ (TangentSpace (𝓡 n) x))) :
      D.curvatureTensor x (b i) (b j) (b k) (b l) = 0 := by
    rw [hindex l k]
    exact D.curvatureTensor_zero_last x (b i) (b j) (b k)
  change Real.sqrt (∑ i, ∑ j, ∑ k, ∑ l,
    (D.curvatureTensor x (b i) (b j) (b k) (b l)) ^ 2) = 0
  simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
    Finset.sum_const_zero, Real.sqrt_zero]

/-- Every represented slice of a low-dimensional Ricci flow has zero full
curvature norm, without completeness or sign hypotheses. -/
theorem RicciFlow.curvatureTensorNorm_eq_zero_of_dimension_le_one
    {J : Set ℝ} (F : RicciFlow n M J) (hn : n ≤ 1) (t : ℝ) (x : M) :
    (F.connection t).curvatureTensorNorm x = 0 :=
  (F.connection t).curvatureTensorNorm_eq_zero_of_dimension_le_one hn x

/-- Zero is a uniform full-curvature bound over all space and time in
dimensions zero and one, and hence on every time slab. -/
theorem RicciFlow.curvatureTensorNorm_bound_zero_of_dimension_le_one
    {J : Set ℝ} (F : RicciFlow n M J) (hn : n ≤ 1) :
    ∀ t : ℝ, ∀ x : M, (F.connection t).curvatureTensorNorm x ≤ 0 := by
  intro t x
  exact le_of_eq (F.curvatureTensorNorm_eq_zero_of_dimension_le_one hn t x)

end PoincareMT
