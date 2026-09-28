import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Fisher
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Kernel.Logarithm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.LeviCivitaData

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [PreconnectedSpace M] [CompactSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {g : RiemannianMetric 2 M}

omit [MeasurableSpace M] [BorelSpace M] [T3Space M] [PreconnectedSpace M] [CompactSpace M] in

theorem contMDiff_log_scalarCurvature (D : LeviCivitaData g)
    (hR : ∀ x, 0 < D.scalarCurvature x) :
    ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ (fun x => Real.log (D.scalarCurvature x)) :=
  fun x => (Real.contDiffAt_log.mpr (hR x).ne').comp_contMDiffAt (D.contMDiff_scalarCurvature x)

theorem integral_log_scalar_mul_laplacian (D : LeviCivitaData g)
    (hR : ∀ x, 0 < D.scalarCurvature x) :
    (∫ x, Real.log (D.scalarCurvature x) * D.laplacian D.scalarCurvature x
      ∂g.volumeMeasure) =
      -(∫ x, g.inner x (D.gradient D.scalarCurvature x) (D.gradient D.scalarCurvature x) /
        D.scalarCurvature x ∂g.volumeMeasure) := by
  rw [D.integral_mul_laplacian (D.contMDiff_log_scalarCurvature hR)
    D.contMDiff_scalarCurvature (HasCompactSupport.of_compactSpace _)]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with x
  have hg := D.gradient_comp ((D.contMDiff_scalarCurvature x).mdifferentiableAt (by simp))
    (Real.differentiableAt_log (hR x).ne')
  change D.gradient (fun x => Real.log (D.scalarCurvature x)) x =
    deriv Real.log (D.scalarCurvature x) • D.gradient D.scalarCurvature x at hg
  rw [hg, Real.deriv_log]
  simp only [map_smul, smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

end PoincareConjecture.LeviCivitaData
