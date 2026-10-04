import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.ProfileCalculus
import PoincareLib.Analysis.Elliptic.Regularity.InteriorEstimates.Sobolev.L2

/-! # Conversion of square-integral estimates to derivative-profile norms -/

noncomputable section

open Set MeasureTheory
open scoped ENNReal
open Poincare.Analysis.Sobolev

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ}
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem derivativeProfile_zero (p : ℝ≥0∞) (V : Set E) (u : E → ℝ) :
    derivativeProfile p V 0 u = eLpNorm u p (volume.restrict V) := by
  simp only [derivativeProfile, Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [show (fun x => ‖iteratedFDeriv ℝ 0 u x‖) = (fun x => ‖u x‖) by
    funext x; rw [norm_iteratedFDeriv_zero]]
  exact eLpNorm_norm (f := u)

end Poincare.Analysis.Elliptic.InteriorEstimates
