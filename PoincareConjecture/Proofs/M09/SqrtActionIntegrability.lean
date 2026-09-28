import PoincareConjecture.Proofs.M09.IntrinsicEnergy
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem curveVelocity_comp_sqrt (α : ℝ → M) (t : ℝ) (ht : 0 < t)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α (Real.sqrt t)) :
    curveVelocity (n := n) (fun r ↦ α (Real.sqrt r)) t =
      (1 / (2 * Real.sqrt t)) • curveVelocity (n := n) α (Real.sqrt t) := by
  have hsqrt := (Real.hasDerivAt_sqrt ht.ne').hasFDerivAt.hasMFDerivAt
  have hsqrtValue : (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) Real.sqrt t) 1 =
      1 / (2 * Real.sqrt t) := by
    exact (congrArg (fun A : ℝ →L[ℝ] ℝ ↦ A 1)
      (mfderiv_eq_fderiv (f := Real.sqrt) (x := t))).trans
      ((congrArg (fun A : ℝ →L[ℝ] ℝ ↦ A 1)
        (Real.hasDerivAt_sqrt ht.ne').hasFDerivAt.fderiv).trans
        (ContinuousLinearMap.toSpanSingleton_apply_one ℝ (1 / (2 * Real.sqrt t))))
  let L : ℝ →L[ℝ] TangentSpace (𝓡 n) (α (Real.sqrt t)) :=
    mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) α (Real.sqrt t)
  have hcomp := congrArg
    (fun A : ℝ →L[ℝ] TangentSpace (𝓡 n) (α (Real.sqrt t)) ↦ A 1)
    (mfderiv_comp t hα hsqrt.mdifferentiableAt)
  have hlin : L (1 / (2 * Real.sqrt t)) = (1 / (2 * Real.sqrt t)) • L 1 := by
    simpa only [smul_eq_mul, mul_one] using L.map_smul (1 / (2 * Real.sqrt t)) (1 : ℝ)
  exact hcomp.trans ((congrArg L hsqrtValue).trans hlin)

set_option backward.isDefEq.respectTransparency false in
theorem backwardLIntegrand_comp_square {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (s : ℝ) (hs : 0 < s)
    (hα : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s) :
    backwardLIntegrand F T (fun r ↦ α (Real.sqrt r)) (s ^ 2) * (2 * s) =
      2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
        (1 / 2 : ℝ) * regularizedCurveEnergy F T α s := by
  have hd : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α (Real.sqrt (s ^ 2)) := by
    simpa only [Real.sqrt_sq hs.le] using hα
  have henergy := congrArg (fun r : ℝ ↦ (F.metric (T - s ^ 2)).inner (α r)
    (curveVelocity (n := n) α r) (curveVelocity (n := n) α r)) (Real.sqrt_sq hs.le)
  unfold backwardLIntegrand regularizedCurveEnergy
  rw [curveVelocity_comp_sqrt α (s ^ 2) (sq_pos_of_pos hs) hd]
  simp only [Real.sqrt_sq hs.le, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  field_simp [hs.ne']
  <;> nlinarith [henergy]

theorem intervalIntegrable_backwardLIntegrand_comp_sqrt {J : Set ℝ}
    (F : RicciFlow n M J) (T b : ℝ) (hb : 0 < b) (α : ℝ → M)
    (hα : ∀ s ∈ Set.Ioo 0 (Real.sqrt b), MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) α s)
    (hR : ContinuousOn (fun s ↦ (F.connection (T - s ^ 2)).scalarCurvature (α s))
      (Set.Icc 0 (Real.sqrt b)))
    (hE : ContinuousOn (regularizedCurveEnergy F T α) (Set.Icc 0 (Real.sqrt b))) :
    IntervalIntegrable (backwardLIntegrand F T (fun r ↦ α (Real.sqrt r)))
      MeasureTheory.volume 0 b := by
  let H : ℝ → ℝ := fun s ↦
    2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
      (1 / 2 : ℝ) * regularizedCurveEnergy F T α s
  have hH : ContinuousOn H (Set.Icc 0 (Real.sqrt b)) :=
    ((continuousOn_const.mul (continuousOn_id.pow 2)).mul hR).add (continuousOn_const.mul hE)
  have hi : IntervalIntegrable
      (fun s ↦ backwardLIntegrand F T (fun r ↦ α (Real.sqrt r)) (s ^ 2) * (2 * s))
      MeasureTheory.volume 0 (Real.sqrt b) := by
    apply (hH.intervalIntegrable_of_Icc (Real.sqrt_nonneg b)).congr_uIoo
    intro s hs
    have hs' : s ∈ Set.Ioo 0 (Real.sqrt b) := by
      simpa only [Set.uIoo_of_le (Real.sqrt_nonneg b)] using hs
    exact (backwardLIntegrand_comp_square F T α s hs'.1 (hα s hs')).symm
  have hsq : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt b)) (max 0 (Real.sqrt b)),
      HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    intro s _
    simpa using hasDerivAt_pow 2 s
  have hpos : ∀ s ∈ Set.Ioo (min 0 (Real.sqrt b)) (max 0 (Real.sqrt b)), 0 ≤ 2 * s := by
    intro s hs
    have hs' : 0 < s := by simpa only [min_eq_left (Real.sqrt_nonneg b)] using hs.1
    positivity
  have h := (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s)
    (g := backwardLIntegrand F T (fun r ↦ α (Real.sqrt r)))
    (continuous_pow 2).continuousOn hsq hpos).mp hi
  simpa only [zero_pow two_ne_zero, Real.sq_sqrt hb.le] using h

end PoincareConjecture.Proofs.M09
