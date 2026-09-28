import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Evolution.Algebra
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Evolution.LogIntegral
import Mathlib.Analysis.Calculus.MeanValue








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [PreconnectedSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}



theorem hasDerivAt_scalarEntropy_surface (F : RicciFlow 2 M J)
    (hpos : ∀ s ∈ interior J, ∀ x, 0 < (F.connection s).scalarCurvature x)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt (fun s => SurfaceEntropy.scalarEntropy (F.connection s))
      ((∫ x, ((F.connection t).scalarCurvature x -
          SurfaceEntropy.meanScalar (F.connection t)) ^ 2 ∂(F.metric t).volumeMeasure) -
        ∫ x, (F.metric t).inner x
          ((F.connection t).gradient (F.connection t).scalarCurvature x)
          ((F.connection t).gradient (F.connection t).scalarCurvature x) /
          (F.connection t).scalarCurvature x ∂(F.metric t).volumeMeasure) t := by
  have hr := SurfaceEntropy.meanScalar_pos (F.connection t) (hpos t ht)
  have h := (F.hasDerivAt_integral_scalar_log_surface hpos ht).sub
    ((F.hasDerivAt_totalScalar_surface ht).mul
      ((F.hasDerivAt_meanScalar_surface ht).log hr.ne'))
  have heq : (fun s => SurfaceEntropy.scalarEntropy (F.connection s)) =ᶠ[nhds t]
      (fun s => (∫ x, (F.connection s).scalarCurvature x *
        Real.log ((F.connection s).scalarCurvature x) ∂(F.metric s).volumeMeasure) -
        (∫ x, (F.connection s).scalarCurvature x ∂(F.metric s).volumeMeasure) *
          Real.log (SurfaceEntropy.meanScalar (F.connection s))) := by
    filter_upwards [isOpen_interior.mem_nhds ht] with s hs
    exact SurfaceEntropy.scalarEntropy_eq_log_integral_sub (F.connection s) (hpos s hs)
  convert h.congr_of_eventuallyEq heq using 1 <;> try rfl
  rw [SurfaceEntropy.integral_scalar_variance_eq]
  simp only [zero_mul, zero_add, pow_two, mul_div_cancel_right₀ _ hr.ne']
  ring

theorem deriv_scalarEntropy_surface_nonpos (F : RicciFlow 2 M J)
    (hpos : ∀ s ∈ interior J, ∀ x, 0 < (F.connection s).scalarCurvature x)
    {t : ℝ} (ht : t ∈ interior J) :
    deriv (fun s => SurfaceEntropy.scalarEntropy (F.connection s)) t ≤ 0 := by
  rw [(F.hasDerivAt_scalarEntropy_surface hpos ht).deriv]
  exact sub_nonpos.mpr ((F.connection t).integral_scalar_variance_le_fisher (hpos t ht)
    (SurfaceEntropy.integral_scalarCurvature_eq_meanScalar_mul_volume (F.connection t)))


theorem antitoneOn_scalarEntropy_surface (F : RicciFlow 2 M J)
    (hJ : Convex ℝ J)
    (hpos : ∀ s ∈ interior J, ∀ x, 0 < (F.connection s).scalarCurvature x) :
    AntitoneOn (fun s => SurfaceEntropy.scalarEntropy (F.connection s)) (interior J) := by
  apply antitoneOn_of_deriv_nonpos hJ.interior
  · intro t ht
    exact (F.hasDerivAt_scalarEntropy_surface hpos ht).continuousAt.continuousWithinAt
  · intro t ht
    exact (F.hasDerivAt_scalarEntropy_surface hpos
      (interior_subset ht)).differentiableAt.differentiableWithinAt
  · intro t ht
    exact F.deriv_scalarEntropy_surface_nonpos hpos (interior_subset ht)

end PoincareConjecture.RicciFlow
