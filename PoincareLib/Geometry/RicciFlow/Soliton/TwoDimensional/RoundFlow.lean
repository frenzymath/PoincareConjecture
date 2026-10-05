import PoincareLib.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Identities
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Homothety of the normalized round ancient surface flow

On a surface with scalar curvature `-1 / t`, the Ricci equation says that
the metric divided by `-t` is constant. The resulting homothety uses the
identity diffeomorphism and the actual time-dependent metric.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle

namespace PoincareMT.RicciFlow

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

/-- The scalar normalization fixes every time-dependent metric coefficient. -/
theorem inner_eq_neg_time_mul_of_scalarCurvature
    (F : RicciFlow 2 M (Set.Iio 0))
    (hR : ∀ t : ℝ, t < 0 → ∀ x : M, (F.connection t).scalarCurvature x = -1 / t)
    (t : ℝ) (ht : t < 0) (x : M) (u v : TangentSpace (𝓡 2) x) :
    (F.metric t).inner x u v = -t * (F.metric (-1)).inner x u v := by
  have hg (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun z => (F.metric z).inner x u v)
        ((F.metric s).inner x u v / s) s := by
    have h := (F.equation s hs x u v).hasDerivAt (isOpen_Iio.mem_nhds hs)
    have hc : -2 * (F.connection s).ricci x u v = (F.metric s).inner x u v / s := by
      rw [(F.connection s).ricci_eq_half_scalarCurvature_mul_inner, hR s hs]
      ring
    rw [hc] at h
    exact h
  have hq (s : ℝ) (hs : s < 0) :
      HasDerivAt (fun z => (F.metric z).inner x u v / (-z)) 0 s := by
    have hs0 : s ≠ 0 := ne_of_lt hs
    have h := (hg s hs).div (hasDerivAt_id s).neg (neg_ne_zero.mpr hs0)
    have hc : ((F.metric s).inner x u v / s * (-s) -
        (F.metric s).inner x u v * (-1)) / (-s) ^ 2 = 0 := by
      field_simp
      ring
    simp only [Pi.neg_apply, id_eq] at h
    rw [hc] at h
    exact h
  have heq := isOpen_Iio.is_const_of_deriv_eq_zero (convex_Iio (0 : ℝ)).isPreconnected
    (fun s hs => (hq s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hq s hs).deriv) ht (show (-1 : ℝ) ∈ Set.Iio 0 by norm_num)
  norm_num only [neg_neg, div_one] at heq
  have h := (div_eq_iff (neg_ne_zero.mpr (ne_of_lt ht))).mp heq
  simpa only [mul_comm] using h

/-- The normalized round ancient surface flow is exactly homothetic to time `-1`. -/
theorem homotheticMetricSlice_of_scalarCurvature
    (F : RicciFlow 2 M (Set.Iio 0))
    (hR : ∀ t : ℝ, t < 0 → ∀ x : M, (F.connection t).scalarCurvature x = -1 / t)
    (t : ℝ) (ht : t < 0) :
    Nonempty (HomotheticMetricSlice (F.metric (-1)) (F.metric t) |t|) := by
  refine ⟨{ map := Diffeomorph.refl (𝓡 2) M ∞, inner_eq := ?_ }⟩
  intro x u v
  simpa only [Diffeomorph.coe_refl, id_eq, mfderiv_id, ContinuousLinearMap.id_apply,
    abs_of_neg ht] using F.inner_eq_neg_time_mul_of_scalarCurvature hR t ht x u v

end PoincareMT.RicciFlow
