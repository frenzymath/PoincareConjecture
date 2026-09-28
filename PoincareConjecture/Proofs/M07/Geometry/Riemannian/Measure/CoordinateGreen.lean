import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Measure.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false

open MeasureTheory
open scoped ContDiff

namespace Poincare

private theorem continuous_mul_of_continuousAt_on_tsupport
    {E : Type*} [TopologicalSpace E] {u f w : E → ℝ}
    (hf : Continuous f) (hs : tsupport f ⊆ tsupport u)
    (hw : ∀ x ∈ tsupport u, ContinuousAt w x) :
    Continuous (fun x ↦ f x * w x) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x ∈ tsupport f
  · exact hf.continuousAt.mul (hw x (hs hx))
  · apply (continuousAt_const (y := (0 : ℝ))).congr_of_eventuallyEq
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp only [hy, Pi.zero_apply, zero_mul]

theorem integral_mul_coordinate_divergence {n : ℕ}
    {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {V : Fin n → EuclideanSpace ℝ (Fin n) → ℝ}
    (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u)
    (hV : ∀ i x, x ∈ tsupport u → ContDiffAt ℝ 1 (V i) x) :
    (∫ x, u x * ∑ i, fderiv ℝ (V i) x (EuclideanSpace.basisFun (Fin n) ℝ i)) =
      -(∫ x, ∑ i, fderiv ℝ u x (EuclideanSpace.basisFun (Fin n) ℝ i) * V i x) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  have hdu (i : Fin n) : Continuous (fun x ↦ fderiv ℝ u x (b i)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdV (i : Fin n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ tsupport u) :
      ContinuousAt (fun x ↦ fderiv ℝ (V i) x (b i)) x :=
    ((hV i x hx).continuousAt_fderiv one_ne_zero).clm_apply continuousAt_const
  have hcont (i : Fin n) : Continuous (fun x ↦ u x * V i x) :=
    continuous_mul_of_continuousAt_on_tsupport hu.continuous (fun _ hx ↦ hx)
      (fun x hx ↦ (hV i x hx).continuousAt)
  have hleft (i : Fin n) : Integrable (fun x ↦ u x * fderiv ℝ (V i) x (b i)) :=
    (continuous_mul_of_continuousAt_on_tsupport hu.continuous (fun _ hx ↦ hx)
      (hdV i)).integrable_of_hasCompactSupport hc.mul_right
  have hright (i : Fin n) : Integrable (fun x ↦ fderiv ℝ u x (b i) * V i x) :=
    (continuous_mul_of_continuousAt_on_tsupport (hdu i)
      (tsupport_fderiv_apply_subset ℝ (b i))
      (fun x hx ↦ (hV i x hx).continuousAt)).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ (b i)).mul_right
  have hparts (i : Fin n) :
      (∫ x, u x * fderiv ℝ (V i) x (b i)) =
        -(∫ x, fderiv ℝ u x (b i) * V i x) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (hright i) (hleft i)
      ((hcont i).integrable_of_hasCompactSupport hc.mul_right)
      (fun x _ ↦ hu.differentiable one_ne_zero x)
      (fun x hx ↦ (hV i x hx).differentiableAt one_ne_zero)
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ ↦ hleft i),
    integral_finsetSum _ (fun i _ ↦ hright i)]
  simp_rw [hparts, Finset.sum_neg_distrib]

end Poincare
