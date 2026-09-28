import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Order.IntermediateValue











set_option autoImplicit false

open Set Filter
open scoped Topology

namespace PoincareConjecture.M35



theorem exists_singular_derivative_of_even
    (f : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
    (hsmooth : ∀ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ContDiffAt ℝ 1 f x)
    (heven : ∀ x, f (-x) = f x) :
    ∃ x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ¬Function.Injective (fderiv ℝ f x) := by
  let d := fun x => (fderiv ℝ f x).det
  have hnegmem (x : EuclideanSpace ℝ (Fin 3))
      (hx : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :
      -x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right, norm_neg] using hx
  have hcontinuous : ContinuousOn d (Metric.sphere 0 1) := by
    intro x hx
    exact (ContinuousLinearMap.continuous_det.continuousAt.comp
      ((hsmooth x hx).continuousAt_fderiv (by norm_num))).continuousWithinAt
  have hodd (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ Metric.sphere 0 1) :
      d (-x) = -d x := by
    have hdf := (hsmooth (-x) (hnegmem x hx)).differentiableAt (by norm_num)
    have hc := hdf.hasFDerivAt.comp x (hasFDerivAt_id x).neg
    have heq : f ∘ Neg.neg = f := funext heven
    rw [heq] at hc
    have hd : -(fderiv ℝ f (-x)) = fderiv ℝ f x := by
      simpa only [ContinuousLinearMap.comp_neg, ContinuousLinearMap.comp_id] using hc.fderiv.symm
    have hd' : fderiv ℝ f (-x) = -(fderiv ℝ f x) := neg_eq_iff_eq_neg.mp hd
    change (fderiv ℝ f (-x)).det = -(fderiv ℝ f x).det
    rw [hd']
    change LinearMap.det (-(fderiv ℝ f x).toLinearMap) =
      -LinearMap.det (fderiv ℝ f x).toLinearMap
    rw [← neg_one_smul ℝ, LinearMap.det_smul]
    norm_num [finrank_euclideanSpace_fin]
  have hconnected : IsPreconnected (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isPreconnected_sphere (by simp [← Module.finrank_eq_rank]) 0 1
  obtain ⟨x, hx⟩ := exists_norm_eq (EuclideanSpace ℝ (Fin 3)) (by norm_num : (0 : ℝ) ≤ 1)
  have hxs : x ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using hx
  have hzero : 0 ∈ d '' Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
    rcases le_total (d x) 0 with hx0 | hx0
    · exact hconnected.intermediate_value hxs (hnegmem x hxs) hcontinuous
        ⟨hx0, by rw [hodd x hxs]; linarith⟩
    · exact hconnected.intermediate_value (hnegmem x hxs) hxs hcontinuous
        ⟨by rw [hodd x hxs]; linarith, hx0⟩
  obtain ⟨y, hy, hdy⟩ := hzero
  refine ⟨y, hy, ?_⟩
  intro hinj
  have hker := LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdy
  exact hker (LinearMap.ker_eq_bot.mpr hinj)

end PoincareConjecture.M35
