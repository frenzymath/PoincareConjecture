import PoincareConjecture.Definitions.M14PathCalculus
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

set_option autoImplicit false

open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

noncomputable def squareRootLIntegrand {p : M14BackwardPath G T τ₁ τ₂ x y}
    (R : M14SquareRootPath G p) (s : ℝ) : ℝ :=
  2 * s ^ 2 * horizontalScalarCurvature G.leafwise (R.curve s) +
    (1 / 2 : ℝ) * G.spacetime.horizontalMetric.inner (R.curve s)
      (R.horizontal_velocity s) (R.horizontal_velocity s)

private theorem inner_transport {q r : G.Point} (h : q = r)
    (v w : G.Horizontal r) :
    G.spacetime.horizontalMetric.inner q (h.symm ▸ v) (h.symm ▸ w) =
      G.spacetime.horizontalMetric.inner r v w := by
  cases h
  rfl

theorem squareRootLIntegrand_eq_transformed
    {p : M14BackwardPath G T τ₁ τ₂ x y} (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    squareRootLIntegrand R s = M14BackwardLIntegrand G p (s ^ 2) * (2 * s) := by
  have hpos : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  have hcurve := R.agrees s ⟨hs.1.le, hs.2.le⟩
  unfold squareRootLIntegrand M14BackwardLIntegrand M14RawLIntegrand
  rw [R.horizontal_agrees s hs, inner_transport hcurve]
  rw [hcurve, Real.sqrt_sq hpos.le]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring

theorem backwardLAction_eq_transformed (p : M14BackwardPath G T τ₁ τ₂ x y) :
    M14BackwardLAction G p =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        M14BackwardLIntegrand G p (s ^ 2) * (2 * s) := by
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := M14BackwardLIntegrand G p) (continuous_id.pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  simpa only [Real.sq_sqrt p.tau_nonneg,
    Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), Function.comp_def,
    M14BackwardLAction] using hsub.symm

theorem integral_squareRootLIntegrand_eq_action
    {p : M14BackwardPath G T τ₁ τ₂ x y} (R : M14SquareRootPath G p) :
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, squareRootLIntegrand R s) =
      M14BackwardLAction G p := by
  rw [backwardLAction_eq_transformed p]
  exact intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.tau_lt.le)
    (fun _ hs => squareRootLIntegrand_eq_transformed R hs)

theorem squareRootLIntegrand_intervalIntegrable
    {p : M14BackwardPath G T τ₁ τ₂ x y} (R : M14SquareRootPath G p) :
    IntervalIntegrable (squareRootLIntegrand R) MeasureTheory.volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
  have hle := Real.sqrt_le_sqrt p.tau_lt.le
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ => s ^ 2) (f' := fun s => 2 * s)
    (g := M14BackwardLIntegrand G p) (continuous_id.pow 2).continuousOn
    (fun s _ => by simpa using hasDerivAt_pow 2 s)
    (fun s hs => by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  have htrans : IntervalIntegrable
      (fun s => M14BackwardLIntegrand G p (s ^ 2) * (2 * s))
      MeasureTheory.volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply hiff.mpr
    simpa only [Real.sq_sqrt p.tau_nonneg,
      Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le),
      M14BackwardLIntegrand] using p.action_integrable
  apply htrans.congr_uIoo
  intro s hs
  rw [Set.uIoo_of_le hle] at hs
  exact (squareRootLIntegrand_eq_transformed R hs).symm

end PoincareConjecture.M14
