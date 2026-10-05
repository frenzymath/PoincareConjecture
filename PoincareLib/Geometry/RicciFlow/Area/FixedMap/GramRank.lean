import PoincareLib.Geometry.Riemannian.MinimalSurface.Sphere.AreaEnergy
import PoincareLib.Geometry.RicciFlow.Basic
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The rank-deficient part of fixed-map variation

Morgan-Tian Claim 18.13, printed p. 427, with the correction recorded in
reviews/errata/2026-09-14-sphere-area.md. Gram rank is independent of the
positive target metric. A fixed rank-deficient differential therefore has
identically zero area along the flow, and the prescribed Ricci-trace
density is zero there as well.
-/

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareMT

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- Nonzero Gram determinant means independence of the actual differential
columns. Source: MT Claim 18.13, p. 427, rank-deficient variation derivation. -/
theorem m60AreaGram_det_ne_zero_iff (g : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) :
    Matrix.det (m60AreaGram g F z) ≠ 0 ↔
      LinearIndependent ℝ (fun i : Fin 2 =>
        mfderiv (𝓡 2) (𝓡 n) F z (EuclideanSpace.basisFun (Fin 2) ℝ i)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  exact Matrix.det_gram_ne_zero_iff_linearIndependent (𝕜 := ℝ)
    (v := fun i : Fin 2 =>
      mfderiv (𝓡 2) (𝓡 n) F z (EuclideanSpace.basisFun (Fin 2) ℝ i))

/-- The degenerate locus of a fixed map does not change with the metric.
Source: MT Claim 18.13, p. 427, rank-deficient variation derivation. -/
theorem m60AreaGram_det_eq_zero_iff (g h : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) :
    Matrix.det (m60AreaGram g F z) = 0 ↔ Matrix.det (m60AreaGram h F z) = 0 := by
  exact not_iff_not.mp
    ((m60AreaGram_det_ne_zero_iff g F z).trans (m60AreaGram_det_ne_zero_iff h F z).symm)

/-- Degeneracy in one metric forces zero area density in every metric.
Source: MT Claim 18.13, p. 427, rank-deficient variation derivation. -/
theorem m60AreaDensity_eq_zero_of_det_eq_zero (g h : RiemannianMetric n M)
    (F : LoopPlane → M) (z : LoopPlane) (hz : Matrix.det (m60AreaGram g F z) = 0) :
    m60AreaDensity h F z = 0 := by
  simp only [m60AreaDensity, (m60AreaGram_det_eq_zero_iff g h F z).mp hz,
    max_self, Real.sqrt_zero]

/-- The Ricci-trace density vanishes at each degenerate differential.
Source: MT Claim 18.13, p. 427, corrected variation convention. -/
theorem m60SphereRicciTraceDensity_eq_zero {g : RiemannianMetric n M}
    (D : LeviCivitaData g) (f : UnitTwoSphere → M) (z : LoopPlane)
    (hz : Matrix.det (m60AreaGram g (f ∘ m60SphereParameter) z) = 0) :
    m60SphereRicciTraceDensity D f z = 0 := by
  simp only [m60SphereRicciTraceDensity, hz, if_true]

/-- The fixed-map variation formula holds pointwise at every degenerate
differential, including endpoints. Source: MT Claim 18.13, p. 427. -/
theorem m60SphereDensity_variation_of_degenerate {J : Set ℝ}
    (F : RicciFlow n M J) (f : UnitTwoSphere → M) (z : LoopPlane) (t : ℝ)
    (hz : Matrix.det (m60AreaGram (F.metric t) (f ∘ m60SphereParameter) z) = 0) :
    HasDerivWithinAt (fun s => m60SphereAreaDensity (F.metric s) f z)
      (-m60SphereRicciTraceDensity (F.connection t) f z) J t := by
  rw [m60SphereRicciTraceDensity_eq_zero (F.connection t) f z hz, neg_zero]
  have hzero : (fun s => m60SphereAreaDensity (F.metric s) f z) = fun _ => (0 : ℝ) := by
    funext s
    exact m60AreaDensity_eq_zero_of_det_eq_zero (F.metric t) (F.metric s)
      (f ∘ m60SphereParameter) z hz
  rw [hzero]
  exact hasDerivWithinAt_const _ _ _

end PoincareMT
