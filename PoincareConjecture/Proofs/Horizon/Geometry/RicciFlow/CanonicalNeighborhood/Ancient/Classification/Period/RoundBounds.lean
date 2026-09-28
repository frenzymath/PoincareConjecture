import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Classification.Surface.Evolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Functional









noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.RicciFlow

variable {N : Type*} [TopologicalSpace N] [MeasurableSpace N] [BorelSpace N]
  [T3Space N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N] [IsManifold (𝓡 2) ∞ N]
  (F : RicciFlow 2 N (Iic 0))
  (hround : ∀ t ≤ 0, ConstantPositiveSectionalCurvature (F.metric t) (F.connection t))

include hround



theorem volumeMeasure_eq_terminal_scale_of_round (p : N) (t : ℝ) (ht : t ≤ 0) :
    (F.metric t).volumeMeasure =
      ENNReal.ofReal (1 - (F.connection 0).scalarCurvature p * t) •
        (F.metric 0).volumeMeasure := by
  obtain ⟨r, hr, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (hround 0 le_rfl)
  have hs : 0 < 1 - (F.connection 0).scalarCurvature p * t := by
    rw [he p]
    nlinarith
  have hmetric : F.metric t = rescaledMetric (F.metric 0)
      (1 - (F.connection 0).scalarCurvature p * t) hs := by
    have hi : (F.metric t).inner = (rescaledMetric (F.metric 0)
        (1 - (F.connection 0).scalarCurvature p * t) hs).inner := by
      funext x
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousLinearMap.ext
      intro w
      change (F.metric t).inner x v w =
        (1 - (F.connection 0).scalarCurvature p * t) * (F.metric 0).inner x v w
      rw [F.inner_eq_terminal_scalar_scale_of_round hround t ht, he x, he p]
    generalize F.metric t = g at hi ⊢
    generalize rescaledMetric (F.metric 0)
      (1 - (F.connection 0).scalarCurvature p * t) hs = h at hi ⊢
    cases g
    cases h
    cases hi
    rfl
  rw [hmetric, SurfaceEntropy.volumeMeasure_rescaled_surface]

omit [MeasurableSpace N] [BorelSpace N] [T3Space N] in


theorem scalarCurvature_le_inv_neg_time_of_round (t : ℝ) (ht : t < 0) (p : N) :
    (F.connection t).scalarCurvature p ≤ (-t)⁻¹ := by
  obtain ⟨r, hr, he⟩ := (constantPositiveSectionalCurvature_iff_scalarCurvature _).mp
    (hround 0 le_rfl)
  have hi := F.inv_scalarCurvature_eq_terminal_sub_time_of_round hround t ht.le p
  rw [he p] at hi
  have heq := congrArg Inv.inv hi
  simp only [inv_inv] at heq
  rw [heq]
  have hrinv := inv_pos.mpr hr
  apply (inv_le_inv₀ (by linarith : 0 < r⁻¹ - t) (neg_pos.mpr ht)).mpr
  linarith

end PoincareConjecture.RicciFlow
