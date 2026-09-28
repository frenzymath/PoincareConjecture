import PoincareConjecture.Definitions.Ch15.SurgeryTopology
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecificLimits.Normed









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Topology
open scoped Manifold ContDiff NNReal

namespace PoincareConjecture.M38

variable (g : StandardCapSpace → StandardCapSpace) {c : ℝ≥0}
  (hg : LipschitzWith c g) (hc : c < 1)

include hg in

theorem smallCoordinateMotion_approximates :
    ApproximatesLinearOn (fun x => x + g x)
      (ContinuousLinearEquiv.refl ℝ StandardCapSpace : StandardCapSpace →L[ℝ] StandardCapSpace)
      Set.univ c := by
  intro x _ y _
  have h := hg.dist_le_mul x y
  simp only [dist_eq_norm] at h
  convert h using 1
  congr 1
  change x + g x - (y + g y) - (x - y) = g x - g y
  abel


noncomputable def smallCoordinateHomeomorph : StandardCapSpace ≃ₜ StandardCapSpace := by
  have hn : ‖((ContinuousLinearEquiv.refl ℝ StandardCapSpace).symm :
      StandardCapSpace →L[ℝ] StandardCapSpace)‖₊ = 1 := by
    change ‖ContinuousLinearMap.id ℝ StandardCapSpace‖₊ = 1
    exact ContinuousLinearMap.nnnorm_id
  exact ApproximatesLinearOn.toHomeomorph (fun x => x + g x)
    (f' := ContinuousLinearEquiv.refl ℝ StandardCapSpace)
    (smallCoordinateMotion_approximates g hg) (Or.inr (by rwa [hn, inv_one]))


theorem smallCoordinateHomeomorph_apply (x : StandardCapSpace) :
    smallCoordinateHomeomorph g hg hc x = x + g x := rfl

include hg hc in

theorem smallCoordinateMotion_derivative_unit (x : StandardCapSpace) :
    IsUnit ((1 : StandardCapSpace →L[ℝ] StandardCapSpace) + fderiv ℝ g x) := by
  have hbound : ‖-fderiv ℝ g x‖ < 1 := by
    rw [norm_neg]
    exact (norm_fderiv_le_of_lipschitz ℝ hg).trans_lt (by exact_mod_cast hc)
  simpa only [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hbound


noncomputable def smallCoordinateDerivative (x : StandardCapSpace) :
    StandardCapSpace ≃L[ℝ] StandardCapSpace :=
  ContinuousLinearEquiv.ofUnit (smallCoordinateMotion_derivative_unit g hg hc x).unit


theorem smallCoordinateDerivative_coe (x : StandardCapSpace) :
    (smallCoordinateDerivative g hg hc x : StandardCapSpace →L[ℝ] StandardCapSpace) =
      1 + fderiv ℝ g x :=
  (smallCoordinateMotion_derivative_unit g hg hc x).unit_spec


theorem smallCoordinateHomeomorph_hasFDerivAt (hsmooth : ContDiff ℝ ∞ g)
    (x : StandardCapSpace) :
    HasFDerivAt (smallCoordinateHomeomorph g hg hc)
      (smallCoordinateDerivative g hg hc x : StandardCapSpace →L[ℝ] StandardCapSpace) x := by
  rw [smallCoordinateDerivative_coe]
  exact (hasFDerivAt_id x).add ((hsmooth.differentiable (by simp)) x).hasFDerivAt


noncomputable def smallCoordinateDiffeomorph (hsmooth : ContDiff ℝ ∞ g) :
    Diffeomorph (𝓡 3) (𝓡 3) StandardCapSpace StandardCapSpace ∞ where
  toEquiv := (smallCoordinateHomeomorph g hg hc).toEquiv
  contMDiff_toFun := contMDiff_iff_contDiff.mpr (contDiff_id.add hsmooth)
  contMDiff_invFun := contMDiff_iff_contDiff.mpr
    ((smallCoordinateHomeomorph g hg hc).contDiff_symm
      (smallCoordinateHomeomorph_hasFDerivAt g hg hc hsmooth) (contDiff_id.add hsmooth))


theorem smallCoordinateDiffeomorph_apply (hsmooth : ContDiff ℝ ∞ g) (x : StandardCapSpace) :
    smallCoordinateDiffeomorph g hg hc hsmooth x = x + g x := rfl


theorem smallCoordinateDiffeomorph_eq_self (hsmooth : ContDiff ℝ ∞ g)
    (x : StandardCapSpace) (hx : g x = 0) :
    smallCoordinateDiffeomorph g hg hc hsmooth x = x := by
  rw [smallCoordinateDiffeomorph_apply, hx, add_zero]

end PoincareConjecture.M38
