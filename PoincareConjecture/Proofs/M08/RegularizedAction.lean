import PoincareConjecture.Definitions.Ch06.LGeometry
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

noncomputable def regularizedLIntegrand {J : Set ℝ} (F : RicciFlow n M J)
    (T : ℝ) (α : ℝ → M) (s : ℝ) : ℝ :=
  2 * s ^ 2 * (F.connection (T - s ^ 2)).scalarCurvature (α s) +
    (1 / 2 : ℝ) * (F.metric (T - s ^ 2)).inner (α s)
      (curveVelocity (n := n) α s) (curveVelocity (n := n) α s)

noncomputable def regularizedLAction {J : Set ℝ} (F : RicciFlow n M J)
    (T τ₁ τ₂ : ℝ) (α : ℝ → M) : ℝ :=
  ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, regularizedLIntegrand F T α s

theorem sq_mem_backward_interior {τ₁ τ₂ s : ℝ} (hτ₁ : 0 ≤ τ₁)
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    0 < s ∧ s ^ 2 ∈ Set.Ioo τ₁ τ₂ := by
  have hpos : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt hs.1
  refine ⟨hpos, Real.lt_sq_of_sqrt_lt hs.1, ?_⟩
  exact (Real.lt_sqrt hpos.le).mp hs.2

theorem curveVelocity_comp_sq {γ : ℝ → M} {s : ℝ}
    (hγ : MDifferentiableAt (𝓘(ℝ, ℝ)) (𝓡 n) γ (s ^ 2)) :
    curveVelocity (n := n) (fun r ↦ γ (r ^ 2)) s =
      (2 * s) • curveVelocity (n := n) γ (s ^ 2) := by
  have hsq : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hsqmf_apply : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun r : ℝ ↦ r ^ 2) s 1 = 2 * s := by
    have hm := hsq.hasFDerivAt.hasMFDerivAt.mfderiv
    have hv := congrArg (fun L : TangentSpace (𝓘(ℝ, ℝ)) s →L[ℝ]
        TangentSpace (𝓘(ℝ, ℝ)) (s ^ 2) ↦ L 1) hm
    change (mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) (fun r : ℝ ↦ r ^ 2) s) (1 : ℝ) =
      (ContinuousLinearMap.toSpanSingleton ℝ (2 * s)) (1 : ℝ) at hv
    simpa only [ContinuousLinearMap.toSpanSingleton_apply, one_smul] using hv
  change (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (γ ∘ fun r : ℝ ↦ r ^ 2) s) 1 = _
  have hchain := mfderiv_comp_apply s (f := fun r : ℝ ↦ r ^ 2) (g := γ)
    hγ hsq.differentiableAt.mdifferentiableAt (1 : TangentSpace (𝓘(ℝ, ℝ)) s)
  have hinput : mfderiv (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ))
      (fun r : ℝ ↦ r ^ 2) s 1 =
      (2 * s) • (1 : TangentSpace (𝓘(ℝ, ℝ)) s) := by
    rw [hsqmf_apply]
    simp
  rw [hinput, map_smul] at hchain
  simpa only [curveVelocity, Function.comp_apply] using hchain

theorem sqrtRegularPath_velocity {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : SqrtRegularPath p) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    curveVelocity (n := n) R.curve s =
      (2 * s) • curveVelocity (n := n) p.curve (s ^ 2) := by
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have hbase : R.curve s = p.curve (s ^ 2) :=
    R.agrees s ⟨hs.1.le, hs.2.le⟩
  have hnear : R.curve =ᶠ[𝓝 s] fun r ↦ p.curve (r ^ 2) :=
    Filter.eventually_of_mem (Ioo_mem_nhds hs.1 hs.2)
      (fun r hr ↦ R.agrees r ⟨hr.1.le, hr.2.le⟩)
  have hγ := (p.regular (s ^ 2) hτ).contMDiffAt (Ioo_mem_nhds hτ.1 hτ.2)
  have hvel : curveVelocity (n := n) R.curve s =
      curveVelocity (n := n) (fun r ↦ p.curve (r ^ 2)) s := by
    unfold curveVelocity
    rw [hnear.mfderiv_eq]
    rfl
  exact hvel.trans (curveVelocity_comp_sq (hγ.mdifferentiableAt one_ne_zero))

theorem regularizedLIntegrand_eq_transformed {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : SqrtRegularPath p) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    regularizedLIntegrand F T R.curve s =
      backwardLIntegrand F T p.curve (s ^ 2) * (2 * s) := by
  have hpos := (sq_mem_backward_interior p.nonnegative hs).1
  have hbase := R.agrees s ⟨hs.1.le, hs.2.le⟩
  have hvel := sqrtRegularPath_velocity R hs
  unfold regularizedLIntegrand backwardLIntegrand
  rw [Real.sqrt_sq hpos.le]
  rw [hbase]
  simp only [hvel, map_smul, smul_apply, smul_eq_mul]
  ring

theorem backwardLLength_eq_transformed {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) :
    backwardLLength F T τ₁ τ₂ p.curve =
      ∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
        backwardLIntegrand F T p.curve (s ^ 2) * (2 * s) := by
  have hle := Real.sqrt_le_sqrt p.ordered.le
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s)
    (g := backwardLIntegrand F T p.curve) (continuous_id.pow 2).continuousOn
    (fun s _ ↦ by simpa using hasDerivAt_pow 2 s)
    (fun s hs ↦ by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  simpa only [Real.sq_sqrt p.nonnegative,
    Real.sq_sqrt (p.nonnegative.trans p.ordered.le), Function.comp_def,
    backwardLLength] using hsub.symm

theorem regularizedLAction_eq_backwardLLength {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : SqrtRegularPath p) :
    regularizedLAction F T τ₁ τ₂ R.curve = backwardLLength F T τ₁ τ₂ p.curve := by
  rw [backwardLLength_eq_transformed p]
  exact intervalIntegral.integral_congr_Ioo_of_le (Real.sqrt_le_sqrt p.ordered.le)
    (fun _ hs ↦ regularizedLIntegrand_eq_transformed R hs)

theorem regularizedLIntegrand_intervalIntegrable {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} {p : BackwardTimePath F T τ₁ τ₂}
    (R : SqrtRegularPath p) :
    IntervalIntegrable (regularizedLIntegrand F T R.curve) MeasureTheory.volume
      (Real.sqrt τ₁) (Real.sqrt τ₂) := by
  have hle := Real.sqrt_le_sqrt p.ordered.le
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (a := Real.sqrt τ₁) (b := Real.sqrt τ₂)
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s)
    (g := backwardLIntegrand F T p.curve) (continuous_id.pow 2).continuousOn
    (fun s _ ↦ by simpa using hasDerivAt_pow 2 s)
    (fun s hs ↦ by
      rw [min_eq_left hle, max_eq_right hle] at hs
      exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le))
  have htrans : IntervalIntegrable
      (fun s ↦ backwardLIntegrand F T p.curve (s ^ 2) * (2 * s))
      MeasureTheory.volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply hiff.mpr
    simpa only [Real.sq_sqrt p.nonnegative,
      Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using p.l_integrable
  apply htrans.congr_uIoo
  intro s hs
  rw [Set.uIoo_of_le hle] at hs
  exact (regularizedLIntegrand_eq_transformed R hs).symm

end PoincareConjecture.M08
