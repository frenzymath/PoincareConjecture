import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Packing
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Nonconjugacy
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.LocalInverse
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity.FrozenMetric
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function Filter MeasureTheory
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pullbackVolumeDensity_le_of_differential_bound
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {x : EuclideanSpace ℝ (Fin n)} {C : ℝ}
    (hi : Function.Injective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hbound : ∀ w : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w) ≤ C * ‖w‖) :
    g.pullbackVolumeDensity f x ≤ (n.factorial : ℝ) * C ^ n := by
  obtain ⟨A, hA, hdet⟩ := g.exists_frozenPullbackEquiv hi
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hentry (i j : Fin n) :
      |LinearMap.toMatrix b.toBasis b.toBasis A.toContinuousLinearMap.toLinearMap i j| ≤ C := by
    rw [LinearMap.toMatrix_apply]
    change |(A (b j)) i| ≤ C
    calc
      |(A (b j)) i| ≤ ‖A (b j)‖ := by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (A (b j)) i
      _ = g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x (b j)) := hA _
      _ ≤ C * ‖b j‖ := hbound _
      _ = C := by simp [b, EuclideanSpace.basisFun_apply]
  have h := Matrix.det_le (abv := AbsoluteValue.abs) hentry
  rw [LinearMap.det_toMatrix] at h
  change |A.toContinuousLinearMap.det| ≤ _ at h
  rw [hdet] at h
  simpa only [Fintype.card_fin, nsmul_eq_mul] using h

theorem mul_volumeMeasure_le_of_differential_bound_of_finite_fibers
    [MeasurableSpace M] [BorelSpace M] [T3Space M]
    (g : RiemannianMetric n M) {f : EuclideanSpace ℝ (Fin n) → M}
    {U : Set (EuclideanSpace ℝ (Fin n))} {S : Set M} {C : ℝ}
    (hU : IsOpen U) (hS : MeasurableSet S)
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f U)
    (hbij : ∀ x ∈ U, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hbound : ∀ x ∈ U, ∀ w : EuclideanSpace ℝ (Fin n),
      g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w) ≤ C * ‖w‖)
    {k : ℕ} (hpreimage : ∀ q ∈ S, ∃ y : Fin k → EuclideanSpace ℝ (Fin n),
      Injective y ∧ ∀ i, y i ∈ U ∧ f (y i) = q) :
    (k : ℝ≥0∞) * g.volumeMeasure S ≤
      ENNReal.ofReal ((n.factorial : ℝ) * C ^ n) * volume U := by
  apply g.mul_volumeMeasure_le_density_bound_of_finite_fibers hU.measurableSet hS
    (fun x hx => (hf.contMDiffAt (hU.mem_nhds hx)).mdifferentiableAt (by simp))
    _ _ hpreimage
  · intro x hx
    obtain ⟨e, hxe, _, heq, _, _⟩ := exists_smooth_inverse_branch hU hf hbij hx
    exact ⟨e.source, e.open_source.mem_nhds hxe,
      e.injOn.congr heq⟩
  · intro x hx
    exact g.pullbackVolumeDensity_le_of_differential_bound (hbij x hx).1 (hbound x hx)

end PoincareConjecture.RiemannianMetric
