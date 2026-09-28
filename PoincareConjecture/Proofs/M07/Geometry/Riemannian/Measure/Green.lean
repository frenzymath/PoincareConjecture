import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.CoordinateGreen
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.HausdorffDensity
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.ScalarOperators.Divergence.Coordinates
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChangeOfVariables
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.ChartSupport
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Green.Local
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {n : ℕ} {g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))}

private theorem fderiv_eq_sum_coordinates
    (L : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    L v = ∑ i, L (EuclideanSpace.basisFun (Fin n) ℝ i) * v i := by
  have h := congrArg L ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, OrthonormalBasis.coe_toBasis,
    OrthonormalBasis.coe_toBasis_repr_apply, EuclideanSpace.basisFun_repr,
    mul_comm] using h.symm



theorem integral_mul_laplacian_density
    (D : LeviCivitaData g)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x * g.pullbackVolumeDensity id x) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) *
        g.pullbackVolumeDensity id x) := by
  let V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ :=
    fun i x => g.pullbackVolumeDensity id x * WithLp.ofLp (D.gradient v x) i
  have hV (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) : ContDiffAt ℝ 1 (V i) x := by
    have hrho := (g.contDiffAt_pullbackVolumeDensity (f := id) (x := x) contMDiffAt_id
      (by simpa using Function.injective_id)).1
    have hgrad := (EuclideanSpace.proj i).contDiff.contDiffAt.comp x
      (D.contDiffAt_gradient_euclidean (hv.contDiffAt))
    exact (hrho.mul hgrad).of_le (by simp)
  have h := Poincare.integral_mul_coordinate_divergence (hu.of_le (by simp)) hc
    (fun i x _ => hV i x)
  have hleft (x : EuclideanSpace ℝ (Fin n)) :
      u x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i) =
        u x * D.laplacian v x * g.pullbackVolumeDensity id x := by
    rw [← D.density_mul_laplacian_eq_divergence hv.contDiffAt]
    ring
  have hright (x : EuclideanSpace ℝ (Fin n)) :
      (∑ i, fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) =
        g.inner x (D.gradient u x) (D.gradient v x) * g.pullbackVolumeDensity id x := by
    rw [D.inner_gradient]
    simp only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    change _ = fderiv ℝ u x (D.gradient v x) * g.pullbackVolumeDensity id x
    rw [fderiv_eq_sum_coordinates, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [V]
    ring
  simpa only [hleft, hright] using h

private theorem volumeMeasure_eq_withDensity
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n))) :
    g.volumeMeasure = volume.withDensity (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) := by
  have h := g.map_restrict_volumeMeasure_symm
    (OpenPartialHomeomorph.refl (EuclideanSpace ℝ (Fin n)))
    contMDiffOn_id contMDiffOn_id
  simpa using h

private theorem integral_volumeMeasure_eq_density
    (g : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ x, f x ∂g.volumeMeasure) = ∫ x, f x * g.pullbackVolumeDensity id x := by
  have hs (x : EuclideanSpace ℝ (Fin n)) := g.contDiffAt_pullbackVolumeDensity
    (f := id) (x := x) contMDiffAt_id (by simpa using Function.injective_id)
  have hm : Measurable (fun x => ENNReal.ofReal (g.pullbackVolumeDensity id x)) :=
    ENNReal.continuous_ofReal.measurable.comp
      (continuous_iff_continuousAt.mpr (fun x => (hs x).1.continuousAt)).measurable
  rw [volumeMeasure_eq_withDensity, integral_withDensity_eq_integral_toReal_smul
    hm (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (le_of_lt (hs _).2), smul_eq_mul, mul_comm]


theorem integral_mul_laplacian_euclidean
    (D : LeviCivitaData g)
    {u v : EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v)
    (hc : HasCompactSupport u) :
    (∫ x, u x * D.laplacian v x ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient u x) (D.gradient v x) ∂g.volumeMeasure) := by
  simp only [integral_volumeMeasure_eq_density]
  exact D.integral_mul_laplacian_density hu hv hc

end PoincareConjecture.LeviCivitaData
