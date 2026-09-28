import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Evolution.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Ancient.Entropy.Evolution.Logarithm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.RicciFlow

variable {M : Type*} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] [CompactSpace M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  {J : Set ℝ}

theorem hasDerivAt_integral_scalar_log_surface (F : RicciFlow 2 M J)
    (hpos : ∀ s ∈ interior J, ∀ x, 0 < (F.connection s).scalarCurvature x)
    {t : ℝ} (ht : t ∈ interior J) :
    HasDerivAt
      (fun s => ∫ x, (F.connection s).scalarCurvature x *
        Real.log ((F.connection s).scalarCurvature x) ∂(F.metric s).volumeMeasure)
      ((∫ x, ((F.connection t).scalarCurvature x) ^ 2 ∂(F.metric t).volumeMeasure) -
        ∫ x, (F.metric t).inner x
          ((F.connection t).gradient (F.connection t).scalarCurvature x)
          ((F.connection t).gradient (F.connection t).scalarCurvature x) /
          (F.connection t).scalarCurvature x ∂(F.metric t).volumeMeasure) t := by
  let D := F.connection t
  let R := D.scalarCurvature
  have hR : ∀ x, 0 < R x := hpos t ht
  have hu : ∀ s ∈ interior J, ∀ x : M,
      ContMDiffAt (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × M => (F.connection p.1).scalarCurvature p.2 *
          Real.log ((F.connection p.1).scalarCurvature p.2)) (s, x) := by
    intro s hs x
    have h := F.contMDiffAt_scalarCurvature_surface hs x
    exact h.mul (LeviCivitaData.contMDiffAt_log_of_pos h (hpos s hs x))
  have hv (x : M) : HasDerivAt
      (fun s => (F.connection s).scalarCurvature x *
        Real.log ((F.connection s).scalarCurvature x))
      ((D.laplacian R x + R x ^ 2) * (Real.log (R x) + 1)) t := by
    have h := F.hasDerivAt_scalarCurvature_surface ht x
    convert h.mul (h.log (hR x).ne') using 1 <;> try rfl
    change (D.laplacian R x + R x ^ 2) * (Real.log (R x) + 1) =
      (D.laplacian R x + R x ^ 2) * Real.log (R x) +
      R x * ((D.laplacian R x + R x ^ 2) / R x)
    field_simp [(hR x).ne']
  have h := F.hasDerivAt_integral_volumeMeasure_surface_of_hasDerivAt ht hu hv
  have hiLap : Integrable (D.laplacian R) (F.metric t).volumeMeasure :=
    (D.contMDiff_laplacian D.contMDiff_scalarCurvature).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiLog : Integrable (fun x => Real.log (R x) * D.laplacian R x)
      (F.metric t).volumeMeasure :=
    ((D.contMDiff_log_scalarCurvature hR).mul
      (D.contMDiff_laplacian D.contMDiff_scalarCurvature)).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hiSq : Integrable (fun x => R x ^ 2) (F.metric t).volumeMeasure :=
    (D.continuous_scalarCurvature.pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have heq : (∫ x, (D.laplacian R x + R x ^ 2) * (Real.log (R x) + 1) -
      R x * (R x * Real.log (R x)) ∂(F.metric t).volumeMeasure) =
      (∫ x, R x ^ 2 ∂(F.metric t).volumeMeasure) -
        ∫ x, (F.metric t).inner x (D.gradient R x) (D.gradient R x) / R x
          ∂(F.metric t).volumeMeasure := by
    calc
      _ = ∫ x, (Real.log (R x) * D.laplacian R x + D.laplacian R x) + R x ^ 2
          ∂(F.metric t).volumeMeasure := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = _ := by
        have hiAdd : Integrable (fun x => Real.log (R x) * D.laplacian R x +
            D.laplacian R x) (F.metric t).volumeMeasure := hiLog.add hiLap
        rw [integral_add hiAdd hiSq, integral_add hiLog hiLap,
          D.integral_laplacian_eq_zero_compact D.contMDiff_scalarCurvature,
          D.integral_log_scalar_mul_laplacian hR]
        ring
  exact heq ▸ h

end PoincareConjecture.RicciFlow
