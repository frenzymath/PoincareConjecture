import PoincareConjecture.Proofs.M08.ReferenceEnergy








set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle intervalIntegral Topology
open MeasureTheory

universe u

namespace PoincareConjecture.M08

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]

theorem squarePath_continuousOn {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) :
    ContinuousOn (squareReparameterizedCurve p.curve) (sqrtParameterInterval τ₁ τ₂) := by
  apply p.continuous.comp (continuous_id.pow 2).continuousOn
  intro s hs
  change τ₁ ≤ s ^ 2 ∧ s ^ 2 ≤ τ₂
  constructor
  · simpa only [Real.sq_sqrt p.nonnegative] using
      (sq_le_sq₀ (Real.sqrt_nonneg τ₁) ((Real.sqrt_nonneg τ₁).trans hs.1)).mpr hs.1
  · simpa only [Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using
      (sq_le_sq₀ ((Real.sqrt_nonneg τ₁).trans hs.1) (Real.sqrt_nonneg τ₂)).mpr hs.2

theorem squarePath_regular {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) 1 (squareReparameterizedCurve p.curve)
      (Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) := by
  exact p.regular.comp ((contDiff_id.pow 2).contMDiff.contMDiffOn)
    (fun s hs ↦ (sq_mem_backward_interior p.nonnegative hs).2)

theorem squarePath_referenceSpeedSq {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂)
    (g : RiemannianMetric n M) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    referenceSpeedSq g (squareReparameterizedCurve p.curve) s =
      2 * ((Real.sqrt (s ^ 2) * referenceSpeedSq g p.curve (s ^ 2)) * (2 * s)) := by
  have hpos := (sq_mem_backward_interior p.nonnegative hs).1
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have hγ := (p.regular _ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)
  have hv := curveVelocity_comp_sq (hγ.mdifferentiableAt one_ne_zero)
  unfold referenceSpeedSq squareReparameterizedCurve
  rw [hv, Real.sqrt_sq hpos.le]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring


theorem squarePath_referenceEnergy {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) (g : RiemannianMetric n M)
    (hW : IntervalIntegrable (fun τ ↦ Real.sqrt τ * referenceSpeedSq g p.curve τ)
      volume τ₁ τ₂) :
    IntervalIntegrable (referenceSpeedSq g (squareReparameterizedCurve p.curve))
      volume (Real.sqrt τ₁) (Real.sqrt τ₂) ∧
    (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      referenceSpeedSq g (squareReparameterizedCurve p.curve) s) =
      2 * ∫ τ in τ₁..τ₂, Real.sqrt τ * referenceSpeedSq g p.curve τ := by
  let W := fun τ ↦ Real.sqrt τ * referenceSpeedSq g p.curve τ
  have hle := Real.sqrt_le_sqrt p.ordered.le
  have hderiv (s : ℝ) : HasDerivAt (fun r : ℝ ↦ r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hnonneg : ∀ s ∈ Set.uIoo (Real.sqrt τ₁) (Real.sqrt τ₂), 0 ≤ 2 * s := by
    intro s hs
    rw [Set.uIoo_of_le hle] at hs
    exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg τ₁).trans hs.1.le)
  have htrans : IntervalIntegrable (fun s ↦ W (s ^ 2) * (2 * s))
      volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := W)
      (continuous_id.pow 2).continuousOn (fun s _ ↦ hderiv s) hnonneg).mpr
    simpa only [Real.sq_sqrt p.nonnegative,
      Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using hW
  have hidentity : (∫ s in Real.sqrt τ₁..Real.sqrt τ₂, W (s ^ 2) * (2 * s)) =
      ∫ τ in τ₁..τ₂, W τ := by
    have h := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := W)
      (continuous_id.pow 2).continuousOn (fun s _ ↦ hderiv s) hnonneg
    simpa only [Function.comp_apply, Real.sq_sqrt p.nonnegative,
      Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using h
  constructor
  · apply (htrans.const_mul 2).congr_uIoo
    intro s hs
    rw [Set.uIoo_of_le hle] at hs
    exact (squarePath_referenceSpeedSq p g hs).symm
  · calc
      _ = ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, 2 * (W (s ^ 2) * (2 * s)) :=
        intervalIntegral.integral_congr_Ioo_of_le hle
          (fun s hs ↦ squarePath_referenceSpeedSq p g hs)
      _ = 2 * ∫ s in Real.sqrt τ₁..Real.sqrt τ₂, W (s ^ 2) * (2 * s) :=
        intervalIntegral.integral_const_mul _ _
      _ = _ := by rw [hidentity]

theorem squarePath_regularizedIntegrand {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) {s : ℝ}
    (hs : s ∈ Set.Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) :
    regularizedLIntegrand F T (squareReparameterizedCurve p.curve) s =
      backwardLIntegrand F T p.curve (s ^ 2) * (2 * s) := by
  have hpos := (sq_mem_backward_interior p.nonnegative hs).1
  have hτ := (sq_mem_backward_interior p.nonnegative hs).2
  have hγ := (p.regular _ hτ).contMDiffAt (isOpen_Ioo.mem_nhds hτ)
  have hv := curveVelocity_comp_sq (hγ.mdifferentiableAt one_ne_zero)
  unfold regularizedLIntegrand backwardLIntegrand squareReparameterizedCurve
  rw [hv, Real.sqrt_sq hpos.le]
  simp only [map_smul, smul_apply, smul_eq_mul]
  ring


theorem squarePath_action {J : Set ℝ} {F : RicciFlow n M J}
    {T τ₁ τ₂ : ℝ} (p : BackwardTimePath F T τ₁ τ₂) :
    IntervalIntegrable (regularizedLIntegrand F T (squareReparameterizedCurve p.curve))
      volume (Real.sqrt τ₁) (Real.sqrt τ₂) ∧
      regularizedLAction F T τ₁ τ₂ (squareReparameterizedCurve p.curve) =
        backwardLLength F T τ₁ τ₂ p.curve := by
  have hle := Real.sqrt_le_sqrt p.ordered.le
  have htrans : IntervalIntegrable
      (fun s ↦ backwardLIntegrand F T p.curve (s ^ 2) * (2 * s))
      volume (Real.sqrt τ₁) (Real.sqrt τ₂) := by
    apply (intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
      (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s)
      (g := backwardLIntegrand F T p.curve) (continuous_id.pow 2).continuousOn
      (fun s _ ↦ by simpa using hasDerivAt_pow 2 s) ?_).mpr
    · simpa only [Real.sq_sqrt p.nonnegative,
        Real.sq_sqrt (p.nonnegative.trans p.ordered.le)] using p.l_integrable
    · intro s hs
      have hspos : 0 < s := (Real.sqrt_nonneg τ₁).trans_lt
        (by simpa [min_eq_left hle] using hs.1)
      exact mul_nonneg (by norm_num) hspos.le
  constructor
  · apply htrans.congr_uIoo
    intro s hs
    rw [Set.uIoo_of_le hle] at hs
    exact (squarePath_regularizedIntegrand p hs).symm
  · rw [backwardLLength_eq_transformed p]
    exact intervalIntegral.integral_congr_Ioo_of_le hle
      (fun s hs ↦ squarePath_regularizedIntegrand p hs)



theorem intervalIntegrable_of_square_transform {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g r : ℝ → ℝ}
    (hr : IntervalIntegrable r volume (Real.sqrt a) (Real.sqrt b))
    (heq : ∀ s ∈ Set.Ioo (Real.sqrt a) (Real.sqrt b),
      r s = g (s ^ 2) * (2 * s)) :
    IntervalIntegrable g volume a b := by
  have hsqrt : Real.sqrt a ≤ Real.sqrt b := Real.sqrt_le_sqrt hab
  have hnonneg : ∀ s ∈ Set.uIoo (Real.sqrt a) (Real.sqrt b), 0 ≤ 2 * s := by
    intro s hs
    rw [Set.uIoo_of_le hsqrt] at hs
    exact mul_nonneg (by norm_num) ((Real.sqrt_nonneg a).trans hs.1.le)
  have hiff := intervalIntegral.integrable_comp_mul_deriv_iff_of_deriv_nonneg
    (f := fun s : ℝ ↦ s ^ 2) (f' := fun s ↦ 2 * s) (g := g)
    (continuous_id.pow 2).continuousOn (fun s _ ↦ by simpa using hasDerivAt_pow 2 s)
    hnonneg
  have htrans : IntervalIntegrable (fun s ↦ g (s ^ 2) * (2 * s)) volume
      (Real.sqrt a) (Real.sqrt b) := by
    apply hr.congr_uIoo
    intro s hs
    rw [Set.uIoo_of_le hsqrt] at hs
    exact heq s hs
  simpa only [Real.sq_sqrt ha, Real.sq_sqrt (ha.trans hab)] using hiff.mp htrans

end PoincareConjecture.M08
