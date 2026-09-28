import PoincareConjecture.Proofs.M34.Standard.ScalarGradientHomothety
import PoincareConjecture.Proofs.M34.Standard.ScalarEvolutionHomothety

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M34

variable {n : ℕ} {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ X] [T2Space X]
  {g : RiemannianMetric n M} {h : RiemannianMetric n X}
  (f : Diffeomorph (𝓡 n) (𝓡 n) M X ∞) (hf : MetricHomothety g h f 1)
  (D : LeviCivitaData g) (D' : LeviCivitaData h)

include hf

theorem metricIsometry_scalar (x : M) : D'.scalarCurvature (f x) = D.scalarCurvature x := by
  symm
  simpa only [div_one] using
    D.scalarCurvature_eq_of_local_homothety D' (by norm_num : (0 : ℝ) < 1)
      isOpen_univ f.contMDiff.contMDiffOn
      (fun y _ v w => by simpa only [one_mul] using (hf y v w).symm) (mem_univ x)

theorem metricIsometry_scalarEvolution (x : M) :
    D'.laplacian D'.scalarCurvature (f x) + 2 * D'.ricciNormSq (f x) =
      D.laplacian D.scalarCurvature x + 2 * D.ricciNormSq x := by
  symm
  simpa only [one_pow, div_one] using
    D.scalarEvolutionNumerator_eq_of_local_homothety D' (by norm_num : (0 : ℝ) < 1)
      isOpen_univ f.contMDiff.contMDiffOn
      (fun y _ v w => by simpa only [one_mul] using (hf y v w).symm) (mem_univ x)

end PoincareConjecture.M34

namespace PoincareConjecture.M34

variable {M X : Type*} [TopologicalSpace M] [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
  [IsManifold (𝓡 3) ∞ M] [IsManifold (𝓡 3) ∞ X] [T2Space X]
  {g : RiemannianMetric 3 M} {h : RiemannianMetric 3 X}
  (f : Diffeomorph (𝓡 3) (𝓡 3) M X ∞) (hf : MetricHomothety g h f 1)
  (D : LeviCivitaData g) (D' : LeviCivitaData h)

include hf

theorem metricIsometry_scalarGradient (x : M) :
    scalarGradientNorm h D' (f x) = scalarGradientNorm g D x := by
  symm
  simpa only [Real.one_rpow, div_one] using
    scalarGradientNorm_eq_of_local_homothety D D' (by norm_num : (0 : ℝ) < 1)
      isOpen_univ f.contMDiff.contMDiffOn
      (fun y _ v w => by simpa only [one_mul] using (hf y v w).symm) (mem_univ x)

theorem metricIsometry_scalarSup (U : Set M) :
    scalarCurvatureSupOn h D' (f '' U) = scalarCurvatureSupOn g D U := by
  simp only [scalarCurvatureSupOn, ← image_eq_range, image_image]
  have heq : (fun x => D'.scalarCurvature (f x)) = D.scalarCurvature := by
    funext x
    exact metricIsometry_scalar f hf D D' x
  rw [heq]

end PoincareConjecture.M34
