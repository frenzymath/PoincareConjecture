import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Density
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.RadialDifferential
import Mathlib.Analysis.InnerProductSpace.NormDet

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackVolumeDensity_eq_abs_det_frame
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (f x))
    (hP : ∀ u v, g.inner (f x) (P u) (P v) = inner ℝ u v) :
    g.pullbackVolumeDensity f x =
      |(P.symm.toContinuousLinearMap.comp (mfderiv (𝓡 n) (𝓡 n) f x)).det| := by
  let A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) :=
    P.symm.toContinuousLinearMap.comp (mfderiv (𝓡 n) (𝓡 n) f x)
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hpair (u v : EuclideanSpace ℝ (Fin n)) :
      g.inner (f x) (mfderiv (𝓡 n) (𝓡 n) f x u)
        (mfderiv (𝓡 n) (𝓡 n) f x v) = inner ℝ (A u) (A v) := by
    simpa only [A, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      P.apply_symm_apply] using! hP (A u) (A v)
  have hgram : Matrix.of (fun i j : Fin n => g.inner (f x)
      (mfderiv (𝓡 n) (𝓡 n) f x (b i)) (mfderiv (𝓡 n) (𝓡 n) f x (b j))) =
      Matrix.gram ℝ (fun i => A (b i)) := by
    ext i j
    exact hpair (b i) (b j)
  change Real.sqrt _ = |A.det|
  rw [hgram]
  erw [← A.toLinearMap.normDet_sq_eq_det_gram b,
    A.toLinearMap.normDet_eq_abs_det]
  simp only [ContinuousLinearMap.det, RCLike.ofReal_real_eq_id, id_eq,
    Real.sqrt_sq_eq_abs, abs_abs]

theorem abs_det_scaled_differential_eq
    (g : RiemannianMetric n M) (f : EuclideanSpace ℝ (Fin n) → M)
    (x : EuclideanSpace ℝ (Fin n))
    (P : EuclideanSpace ℝ (Fin n) ≃L[ℝ] TangentSpace (𝓡 n) (f x))
    (hP : ∀ u v, g.inner (f x) (P u) (P v) = inner ℝ u v)
    {t : ℝ} (ht : 0 ≤ t) :
    |(t • (P.symm.toContinuousLinearMap.comp (mfderiv (𝓡 n) (𝓡 n) f x))).det| =
      t ^ n * g.pullbackVolumeDensity f x := by
  rw [g.pullbackVolumeDensity_eq_abs_det_frame f x P hP]
  simp only [TangentSpace]
  rw [ContinuousLinearMap.det, ContinuousLinearMap.toLinearMap_smul,
    LinearMap.det_smul, abs_mul, abs_pow, abs_of_nonneg ht]
  simp only [finrank_euclideanSpace, Fintype.card_fin, ContinuousLinearMap.det]

end PoincareConjecture.RiemannianMetric
