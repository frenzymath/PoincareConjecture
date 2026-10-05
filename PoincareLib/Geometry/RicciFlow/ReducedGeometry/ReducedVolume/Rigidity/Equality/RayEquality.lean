import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedVolume.Comparison.VolumeComparison
import Mathlib.MeasureTheory.Measure.OpenPos

/-!
# Equality of the actual weighted rays

Morgan-Tian Theorem 7.26 and Proposition 7.27, pp. 165-167. Equality in the
global Gaussian comparison forces equality almost everywhere on the source.
The Gaussian is positive, so the canonical regular source is conull. The
raw weight is continuous on every initial vector, which makes its equality
pointwise, including initial vectors outside the canonical regular source.
-/

set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareMT.ReducedVolume

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

/-- Equality at one time persists at every earlier positive time. -/
theorem reducedVolume_eq_euclidean_of_le
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {b τ : ℝ} (hb : 0 < b) (hbmax : b < τmax) (hτ : 0 < τ) (hτb : τ ≤ b)
    (heq : reducedVolume F T p b = euclideanReducedVolume n) :
    reducedVolume F T p τ = euclideanReducedVolume n := by
  apply le_antisymm
    (reducedVolume_le_euclidean hL hDifferential G hmax hT hwindow hcurvature
      hτ (hτb.trans_lt hbmax))
  rw [← heq]
  exact reducedVolume_antitoneOn hL hDifferential G hmax hT hwindow hcurvature
    ⟨hτ, hτb.trans_lt hbmax⟩ ⟨hb, hbmax⟩ hτb

/-- Equality in integral comparison makes the zero extension Gaussian almost everywhere. -/
theorem regularWeightedJacobian_ae_eq_gaussian_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax)
    (heq : reducedVolume F T p τ = euclideanReducedVolume n) :
    regularWeightedJacobian G τ =ᵐ[volume]
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)) := by
  apply (integral_eq_iff_of_ae_le
    (regularWeightedJacobian_integrable hL hDifferential G hmax hT hwindow hcurvature hτ hτmax)
    (sourceGaussian_integrable n)
    (ae_of_all _ (regularWeightedJacobian_le_sourceGaussian hL hDifferential G hmax hT
      hwindow hcurvature τ))).mp
  rw [← reducedVolume_eq_integral_regularWeight hL hDifferential G hmax hT hwindow
    hcurvature hτ hτmax, integral_sourceGaussian, heq]

omit [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- A Gaussian zero extension forces the actual regular source to be conull. -/
theorem ae_mem_exponentialSlice_source_of_gaussian
    (G : LExponentialGeometry F T τmax p) {τ : ℝ}
    (heq : regularWeightedJacobian G τ =ᵐ[volume]
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))) :
    ∀ᵐ x, x ∈ (exponentialSliceChart G τ).source := by
  classical
  filter_upwards [heq] with x hx
  by_contra hmem
  have hz : regularWeightedJacobian G τ x = 0 := indicator_of_notMem hmem _
  exact (sourceGaussian_pos n x).ne' (hz ▸ hx).symm

omit [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Full-source continuity upgrades Gaussian equality to raw pointwise equality. -/
theorem weightedExponentialJacobian_eq_gaussian_of_ae
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax)
    (heq : regularWeightedJacobian G τ =ᵐ[volume]
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))) :
    weightedExponentialJacobian G τ =
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)) := by
  have hmem := ae_mem_exponentialSlice_source_of_gaussian G heq
  have hg : Continuous (fun x : EuclideanSpace ℝ (Fin n) ↦
      (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)) := by fun_prop
  apply Measure.eq_of_ae_eq (μ := volume) ?_
    (weightedExponentialJacobian_continuous G hτ hτmax) hg
  filter_upwards [heq, hmem] with x hx hxs
  simpa only [regularWeightedJacobian, indicator_of_mem hxs] using hx

/-- Maximal reduced volume gives the exact Gaussian weight at every source vector. -/
theorem weightedExponentialJacobian_eq_gaussian_of_volume_eq
    (hL : LGeodesicTheory F T τmax) (hDifferential : ReducedLengthDifferentialTheory F T τmax)
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    {τ : ℝ} (hτ : 0 < τ) (hτmax : τ < τmax)
    (heq : reducedVolume F T p τ = euclideanReducedVolume n) :
    weightedExponentialJacobian G τ =
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)) :=
  weightedExponentialJacobian_eq_gaussian_of_ae G hτ hτmax
    (regularWeightedJacobian_ae_eq_gaussian_of_volume_eq hL hDifferential G hmax hT
      hwindow hcurvature hτ hτmax heq)

omit [T3Space M] [ConnectedSpace M] [MeasurableSpace M] [BorelSpace M] in
/-- Pointwise Gaussian equality makes the actual Gram Jacobian strictly positive everywhere. -/
theorem exponentialSliceJacobian_pos_of_gaussian
    (G : LExponentialGeometry F T τmax p) {τ : ℝ} (hτ : 0 < τ)
    (heq : weightedExponentialJacobian G τ =
      (fun x : EuclideanSpace ℝ (Fin n) ↦ (2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2)))
    (x : EuclideanSpace ℝ (Fin n)) : 0 < exponentialSliceJacobian G τ x := by
  have hw : 0 < weightedExponentialJacobian G τ x := by
    rw [heq]
    exact sourceGaussian_pos n x
  exact pos_of_mul_pos_right hw
    (mul_pos (Real.rpow_pos_of_pos hτ _) (Real.exp_pos _)).le

end PoincareMT.ReducedVolume
