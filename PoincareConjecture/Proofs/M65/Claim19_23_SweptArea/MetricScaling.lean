import PoincareConjecture.Definitions.M60Area
import PoincareConjecture.Proofs.M65.Mathlib.GramComparison










set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem m65AreaDensityScaling_of_metric_comparison
    (g h : RiemannianMetric n M) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x), h.inner x v v ≤ C * g.inner x v v)
    (f : LoopPlane → M) (z : LoopPlane) :
    m60AreaDensity h f z ≤ C * m60AreaDensity g f z := by
  let e : Fin 2 → TangentSpace (𝓡 n) (f z) :=
    fun i => mfderiv (𝓡 2) (𝓡 n) f z (EuclideanSpace.basisFun (Fin 2) ℝ i)
  have hdet : (m60AreaGram h f z).det ≤ C ^ 2 * (m60AreaGram g f z).det := by
    have hh := ContinuousLinearMap.gramDet_two_le_of_quadratic_bound
      (g.inner (f z)) (h.inner (f z)) (g.symm (f z)) (h.symm (f z)) (g.pos (f z))
      (h.toRiemannianMetric.toCore (f z)).re_inner_nonneg hC (hbound (f z)) (e 0) (e 1)
    change (Matrix.det fun i j => h.inner (f z) (e i) (e j)) ≤
      C ^ 2 * (Matrix.det fun i j => g.inner (f z) (e i) (e j))
    erw [Matrix.det_fin_two, Matrix.det_fin_two]
    simpa only [h.symm (f z) (e 1) (e 0), g.symm (f z) (e 1) (e 0), pow_two] using hh
  have hmax : max 0 (m60AreaGram h f z).det ≤ C ^ 2 * max 0 (m60AreaGram g f z).det :=
    max_le (mul_nonneg (sq_nonneg _) (le_max_left _ _))
      (hdet.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (sq_nonneg _)))
  calc
    _ ≤ Real.sqrt (C ^ 2 * max 0 (m60AreaGram g f z).det) := Real.sqrt_le_sqrt hmax
    _ = C * m60AreaDensity g f z := by
      rw [Real.sqrt_mul (sq_nonneg C), Real.sqrt_sq hC]
      rfl



theorem m65AreaScaling_of_metric_comparison
    (g h : RiemannianMetric n M) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ x (v : TangentSpace (𝓡 n) x), h.inner x v v ≤ C * g.inner x v v)
    (f : LoopPlane → M) (domain : Set LoopPlane)
    (hg : IntegrableOn (m60AreaDensity g f) domain volume)
    (hh : IntegrableOn (m60AreaDensity h f) domain volume) :
    (∫ z in domain, m60AreaDensity h f z) ≤ C * ∫ z in domain, m60AreaDensity g f z := by
  rw [← integral_const_mul]
  exact integral_mono hh (hg.const_mul C)
    (m65AreaDensityScaling_of_metric_comparison g h hC hbound f)

end PoincareConjecture
