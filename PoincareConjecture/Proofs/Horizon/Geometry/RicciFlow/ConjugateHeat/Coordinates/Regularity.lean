import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.ConjugateHeat.Coordinates.Operator
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Topology
open Poincare.Analysis.Parabolic.WeakRegularity

namespace PoincareConjecture.RicciFlow.BackwardCoordinates

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} (F : RicciFlow n M J)
  (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
  (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
  (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)

include he hei


theorem contDiffOn_of_weak_heat_pairing
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    {w : Spacetime n → ℝ} (hw : ContinuousOn w U)
    (hweak : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ z in U, w z * (-Canonical.timeDeriv φ z -
        (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1))) = 0) :
    ContDiffOn ℝ ∞ w U := by
  apply Canonical.contDiffOn_of_weak_forward_equation hU
    (fun i j => (contDiffOn_principal F e he hei i j).mono hUD)
    (fun i => (contDiffOn_drift F e he hei i).mono hUD)
    (fun z hz v hv => principal_pos F e he hei (hUD hz).1 v hv) hw
  intro φ hφ hφc hφU
  convert hweak φ hφ hφc hφU using 1
  apply setIntegral_congr_fun hU.measurableSet
  intro z hz
  dsimp only
  rw [laplacian_coordinateTest_forward F e he hei hφ (hUD hz)]
  ring



theorem potential_contDiffOn_of_weak_heat_pairing
    {U : Set (Spacetime n)} (hU : IsOpen U) (hUD : U ⊆ domain J e)
    (hUt : ∀ z ∈ U, 0 < z.2)
    {l : Spacetime n → ℝ} (hl : ContinuousOn l U)
    (hweak : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U →
      (∫ z in U, (density F e z * z.2 ^ (-(n : ℝ) / 2) * Real.exp (-l z)) *
        (-Canonical.timeDeriv φ z -
          (F.connection (-z.2)).laplacian (fun y => φ (e.symm y, z.2)) (e z.1))) = 0) :
    ContDiffOn ℝ ∞ l U := by
  let v : Spacetime n → ℝ := fun z => density F e z * z.2 ^ (-(n : ℝ) / 2)
  let w : Spacetime n → ℝ := fun z => v z * Real.exp (-l z)
  have hv : ContDiffOn ℝ ∞ v U :=
    ((contDiffOn_density F e he hei).mono hUD).mul
      (contDiffOn_snd.rpow_const_of_ne (fun z hz => (hUt z hz).ne'))
  have hvpos (z) (hz : z ∈ U) : 0 < v z :=
    mul_pos (density_pos F e he hei (hUD hz).1) (Real.rpow_pos_of_pos (hUt z hz) _)
  have hw : ContDiffOn ℝ ∞ w U :=
    contDiffOn_of_weak_heat_pairing F e he hei hU hUD
      (hv.continuousOn.mul (Real.continuous_exp.comp_continuousOn hl.neg)) hweak
  have hquot : ∀ z ∈ U, w z / v z = Real.exp (-l z) := by
    intro z hz
    dsimp only [w]
    exact mul_div_cancel_left₀ _ (hvpos z hz).ne'
  have hlog := ((hw.div hv (fun z hz => (hvpos z hz).ne')).log
    (fun z hz => by
      change w z / v z ≠ 0
      rw [hquot z hz]
      exact (Real.exp_pos _).ne')).neg
  apply hlog.congr
  intro z hz
  change l z = -Real.log (w z / v z)
  rw [hquot z hz, Real.log_exp, neg_neg]

end PoincareConjecture.RicciFlow.BackwardCoordinates
