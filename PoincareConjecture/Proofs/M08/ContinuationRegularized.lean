import PoincareConjecture.Proofs.M08.ContinuationCurve
import PoincareConjecture.Proofs.M08.FirstVariationIdentity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Topology
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem regularizedData_isContinuationCurve {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J) (hτ₂ : τ₂ ≤ τmax)
    (p : BackwardTimePath F T τ₁ τ₂) (R : RegularizedLGeodesicData p) :
    IsContinuationCurve F T R.path.curve (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
  let I := Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)
  let C := sqrtParameterInterval τ₁ τ₂
  have hIC : I ⊆ C := Ioo_subset_Icc_self
  let E := restrictInteriorVelocityExtension isOpen_Ioo hIC R.path.curve R.velocity_extension
  apply isContinuationCurve_of_regularizedEuler F hM04 T isOpen_Ioo R.path.curve
    (R.path.smooth.mono (hIC.trans R.path.interval_subset))
    (fun s hs ↦ backwardSquareTime_mem_interior hwindow p.nonnegative p.ordered hτ₂ hs) E
  intro s hs W
  have h := R.equation s (hIC hs) W
  unfold regularizedLGeodesicEquation at h
  change regularizedEulerResidual F T R.path.curve I E s W = 0
  unfold regularizedEulerResidual pullbackCovariantDerivative E restrictInteriorVelocityExtension
  rw [curveVelocityWithin_eq_of_open_subset isOpen_Ioo hIC R.path.curve hs]
  exact h

theorem regularizedSquare_isContinuationCurve {J : Set ℝ} {F : RicciFlow n M J}
    {T τmax τ₁ τ₂ : ℝ} (hM04 : RicciFlowCurvatureTheory.{u})
    (hwindow : Icc (T - τmax) T ⊆ J) (hτ₂ : τ₂ ≤ τmax)
    (p : BackwardTimePath F T τ₁ τ₂) (R : RegularizedLGeodesicData p) :
    IsContinuationCurve F T (squareReparameterizedCurve p.curve)
      (Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
  apply (regularizedData_isContinuationCurve hM04 hwindow hτ₂ p R).congr isOpen_Ioo
  intro s hs
  exact (R.path.agrees s (Ioo_subset_Icc_self hs)).symm

end PoincareConjecture.M08
