import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Weighted.Semigroup
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.Pointwise.Time
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Kernel.L2

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

private theorem integral_mul_le_l2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f q : X → ℝ} (hf : MemLp f 2 μ) (hq : MemLp q 2 μ) :
    (∫ x, f x * q x ∂μ) ≤ (eLpNorm f 2 μ).toReal * (eLpNorm q 2 μ).toReal := by
  have he : (∫ x, f x * q x ∂μ) = ⟪hf.toLp f, hq.toLp q⟫_ℝ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, hq.coeFn_toLp] with x hx hy
    simp [hx, hy, mul_comm]
  rw [he, ← Lp.norm_toLp, ← Lp.norm_toLp]
  exact real_inner_le_norm _ _

private theorem eLpNorm_indicator_exp_le {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {A : Set X} (hA : MeasurableSet A) (hAfin : μ A ≠ ⊤)
    {ψ : X → ℝ} {a : ℝ} (ha : ∀ x ∈ A, ψ x ≤ a) :
    (eLpNorm (A.indicator (fun x => Real.exp (ψ x))) 2 μ).toReal ≤
      Real.exp a * Real.sqrt (μ.real A) := by
  have hC := memLp_indicator_const (μ := μ) 2 hA (Real.exp a) (Or.inr hAfin)
  have hm : eLpNorm (A.indicator (fun x => Real.exp (ψ x))) 2 μ ≤
      eLpNorm (A.indicator (fun _ => Real.exp a)) 2 μ := by
    apply eLpNorm_mono
    intro x
    by_cases hx : x ∈ A
    · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (ha x hx)
    · simp [hx]
  have h := ENNReal.toReal_mono hC.eLpNorm_lt_top.ne hm
  rw [eLpNorm_indicator_const hA (by norm_num) (by norm_num)] at h
  simpa [ENNReal.toReal_mul, ENNReal.toReal_rpow, Real.sqrt_eq_rpow,
    Measure.real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using h

private theorem setIntegral_restrict_eq_of_zero {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {A Ω : Set X} (hA : MeasurableSet A) (hΩ : MeasurableSet Ω)
    {f : X → ℝ} (hf : ∀ x ∉ Ω, f x = 0) :
    (∫ x in A, f x ∂μ.restrict Ω) = ∫ x in A, f x ∂μ := by
  rw [Measure.restrict_restrict hA, inter_comm A Ω, ← Measure.restrict_restrict hΩ]
  exact setIntegral_eq_integral_of_forall_compl_eq_zero hf

universe u

variable {n : ℕ} [NeZero n] {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {Ω : Set M}

theorem setIntegral_setIntegral_heatKernelContinuousTime_le
    (D : LeviCivitaData g) (S : Poincare.Manifold.SmoothDomain n Ω)
    {A B : Set M} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAfin : g.volumeMeasure A ≠ ⊤) (hBfin : g.volumeMeasure B ≠ ⊤)
    (ψ : M → ℝ) (hψ : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ ψ)
    (L : ℝ) (hL : 0 ≤ L)
    (hgrad : ∀ x ∈ Ω, g.inner x (D.gradient ψ x) (D.gradient ψ x) ≤ L ^ 2)
    {a b t : ℝ} (ha : ∀ x ∈ A, ψ x ≤ a) (hb : ∀ y ∈ B, b ≤ ψ y)
    (ht : 0 < t) :
    (∫ x in A, ∫ y in B, heatKernelContinuousTime D S t x y
      ∂g.volumeMeasure ∂g.volumeMeasure) ≤
      Real.sqrt (g.volumeMeasure.real A) * Real.sqrt (g.volumeMeasure.real B) *
        Real.exp (L ^ 2 * t + a - b) := by
  let ν := g.volumeMeasure.restrict Ω
  let : IsFiniteMeasure ν := domainMeasure_isFinite Ω S.isCompact_closure
  let hn := Nat.pos_of_ne_zero (NeZero.ne n)
  have hf : MemLp (B.indicator (fun _ : M => (1 : ℝ))) 2 ν :=
    memLp_indicator_const 2 hB 1 (Or.inr (measure_ne_top _ _))
  let f := hf.toLp (B.indicator (fun _ : M => (1 : ℝ)))
  let P := heatSemigroup D Ω hn S.isOpen S.isCompact_closure t.toNNReal f
  let U := Boundary.heatPowerContinuous D S 0 t ht f
  have hU : (U : M → ℝ) =ᵐ[ν] (P : M → ℝ) := by
    have h := Boundary.heatPowerContinuous_ae D S 0 t ht f
    rw [heatSpectralPower_zero_eq_heatSemigroup D Ω hn S.isOpen S.isCompact_closure ht] at h
    exact h
  have hrow (x : M) : (∫ y in B, heatKernelContinuousTime D S t x y ∂g.volumeMeasure) = U x := by
    simp only [heatKernelContinuousTime_of_pos D S ht]
    rw [← setIntegral_restrict_eq_of_zero hB S.isOpen.measurableSet
      (fun y hy => heatKernelContinuous_zero D S t ht x y (Or.inr hy))]
    rw [← integral_indicator hB, ← integral_heatKernelContinuous_mul D S t ht x f]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with y hy
    change B.indicator (heatKernelContinuous D S t ht x) y =
      heatKernelContinuous D S t ht x y * f y
    rw [hy]
    by_cases hyB : y ∈ B <;> simp [hyB]
  have houter : (∫ x in A, U x ∂g.volumeMeasure) = ∫ x in A, P x ∂ν := by
    rw [← setIntegral_restrict_eq_of_zero hA S.isOpen.measurableSet
      (fun x hx => Boundary.heatPowerContinuous_zero_outside D S 0 t ht f x hx)]
    exact integral_congr_ae (ae_restrict_of_ae hU)
  have hneg (x : M) : D.gradient (fun y => -ψ y) x = -D.gradient ψ x := by
    apply (g.inner_isInvertible x).injective
    ext v
    rw [D.inner_gradient]
    rw [show (fun y => -ψ y) = (-ψ) by rfl, mvfderiv_neg]
    simp [D.inner_gradient]
  have hgrad' : ∀ x ∈ Ω, g.inner x (D.gradient (fun y => -ψ y) x)
      (D.gradient (fun y => -ψ y) x) ≤ L ^ 2 := by
    intro x hx
    simpa only [hneg, map_neg, neg_apply, neg_neg] using hgrad x hx
  let q := fun x => Real.exp (-ψ x) * P x
  have hq : MemLp q 2 ν :=
    memLp_continuous_mul S.isOpen S.isCompact_closure _
      (Real.continuous_exp.comp hψ.continuous.neg) P
  let w := A.indicator (fun x => Real.exp (ψ x))
  have hw : MemLp w 2 ν := by
    have hC := memLp_indicator_const (μ := ν) 2 hA (Real.exp a)
      (Or.inr (measure_ne_top _ _))
    refine hC.of_le ((Real.continuous_exp.comp hψ.continuous).aestronglyMeasurable.indicator hA) ?_
    filter_upwards with x
    by_cases hx : x ∈ A
    · simp only [w, Set.indicator_of_mem hx, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_exp.mpr (ha x hx)
    · simp [w, hx]
  have hpair : (∫ x in A, P x ∂ν) = ∫ x, w x * q x ∂ν := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ A
    · simp only [w, q, Set.indicator_of_mem hx]
      rw [← mul_assoc, ← Real.exp_add]
      simp
    · simp [w, hx]
  have hweighted := weighted_heatSemigroup_norm_le D Ω hn S.isOpen S.isCompact_closure
    (fun y => -ψ y) hψ.neg L hL hgrad' f t ht
  have hinput : (fun x => Real.exp (-ψ x) * f x) =ᵐ[ν]
      B.indicator (fun x => Real.exp (-ψ x)) := by
    filter_upwards [hf.coeFn_toLp] with x hx
    rw [hx]
    by_cases hxB : x ∈ B <;> simp [hxB]
  rw [eLpNorm_congr_ae hinput] at hweighted
  have hwbound := eLpNorm_indicator_exp_le (μ := ν) hA (measure_ne_top _ _) ha
  have hfbound := eLpNorm_indicator_exp_le (μ := ν) hB (measure_ne_top _ _)
    (fun y hy => neg_le_neg (hb y hy))
  have hνA' : ν A ≤ g.volumeMeasure A := by
    rw [show ν = g.volumeMeasure.restrict Ω by rfl, Measure.restrict_apply hA]
    exact measure_mono inter_subset_left
  have hνB' : ν B ≤ g.volumeMeasure B := by
    rw [show ν = g.volumeMeasure.restrict Ω by rfl, Measure.restrict_apply hB]
    exact measure_mono inter_subset_left
  have hνA : ν.real A ≤ g.volumeMeasure.real A := ENNReal.toReal_mono hAfin hνA'
  have hνB : ν.real B ≤ g.volumeMeasure.real B := ENNReal.toReal_mono hBfin hνB'
  have hqb : (eLpNorm q 2 ν).toReal ≤
      Real.exp (L ^ 2 * t) * (Real.exp (-b) * Real.sqrt (ν.real B)) :=
    hweighted.trans (mul_le_mul_of_nonneg_left hfbound (Real.exp_nonneg _))
  calc
    (∫ x in A, ∫ y in B, heatKernelContinuousTime D S t x y
        ∂g.volumeMeasure ∂g.volumeMeasure) = ∫ x in A, P x ∂ν := by
      simp_rw [hrow]
      exact houter
    _ = ∫ x, w x * q x ∂ν := hpair
    _ ≤ (eLpNorm w 2 ν).toReal * (eLpNorm q 2 ν).toReal := integral_mul_le_l2 hw hq
    _ ≤ (Real.exp a * Real.sqrt (ν.real A)) *
        (Real.exp (L ^ 2 * t) * (Real.exp (-b) * Real.sqrt (ν.real B))) :=
      mul_le_mul hwbound hqb ENNReal.toReal_nonneg
        (mul_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _))
    _ = Real.sqrt (ν.real A) * Real.sqrt (ν.real B) * Real.exp (L ^ 2 * t + a - b) := by
      rw [show L ^ 2 * t + a - b = a + (L ^ 2 * t + -b) by ring]
      simp only [Real.exp_add]
      ring
    _ ≤ Real.sqrt (g.volumeMeasure.real A) * Real.sqrt (g.volumeMeasure.real B) *
        Real.exp (L ^ 2 * t + a - b) :=
      mul_le_mul_of_nonneg_right (mul_le_mul (Real.sqrt_le_sqrt hνA)
        (Real.sqrt_le_sqrt hνB) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
          (Real.exp_nonneg _)

end PoincareConjecture.LeviCivitaData.Dirichlet
