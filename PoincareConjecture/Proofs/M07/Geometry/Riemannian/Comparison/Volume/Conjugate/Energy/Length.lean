import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.GeodesicLength
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal Bundle

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem pathELength_eq_ofReal_integral_speed
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn (fun t =>
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) (Icc a b)) :
    g.pathELength γ a b = ENNReal.ofReal (∫ t in a..b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) := by
  rw [pathELength_eq_lintegral_tangentNorm, intervalIntegral.integral_of_le hab,
    ← integral_Icc_eq_integral_Ioc]
  symm
  apply ofReal_integral_eq_lintegral_ofReal hcont.integrableOn_Icc
  exact Filter.Eventually.of_forall fun _ => Real.sqrt_nonneg _

theorem edist_le_ofReal_integral_speed
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hcont : ContinuousOn (fun t =>
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) (Icc a b)) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal (∫ t in a..b,
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  rw [← g.pathELength_eq_ofReal_integral_speed hab hcont]
  exact Manifold.riemannianEDist_le_pathELength hγ rfl rfl hab

theorem edist_le_ofReal_energy_bound
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b C : ℝ}
    (hab : a ≤ b) (hC : 0 < C)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b))
    (hcont : ContinuousOn (fun t =>
      g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) (Icc a b)) :
    g.edist (γ a) (γ b) ≤ ENNReal.ofReal
      (((∫ t in a..b,
        (g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)) ^ 2) +
          (b - a) * C ^ 2) / (2 * C)) := by
  let s : ℝ → ℝ := fun t => g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
  have hs : IntervalIntegrable s volume a b := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le hab] using hcont
  have hs2 : IntervalIntegrable (fun t => s t ^ 2) volume a b := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab]
    exact hcont.pow 2
  refine (g.edist_le_ofReal_integral_speed hab hγ hcont).trans
    (ENNReal.ofReal_le_ofReal ?_)
  change (∫ t in a..b, s t) ≤ ((∫ t in a..b, s t ^ 2) + (b - a) * C ^ 2) / (2 * C)
  apply (le_div_iff₀ (by positivity : 0 < 2 * C)).mpr
  have h := intervalIntegral.integral_mono_on hab (hs.const_mul (2 * C))
    (hs2.add intervalIntegrable_const)
    (fun t _ => show 2 * C * s t ≤ s t ^ 2 + C ^ 2 by nlinarith [sq_nonneg (s t - C)])
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_add hs2 intervalIntegrable_const,
    intervalIntegral.integral_const] at h
  simpa only [smul_eq_mul, mul_comm] using h

end PoincareConjecture.RiemannianMetric

namespace Poincare.VolumeComparison.Conjugate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem edist_le_ofReal_sum
    (g : PoincareConjecture.RiemannianMetric n M) (p : ℕ → M) (l : ℕ → ℝ)
    (N : ℕ) (hl : ∀ i < N, 0 ≤ l i)
    (hd : ∀ i < N, g.edist (p i) (p (i + 1)) ≤ ENNReal.ofReal (l i)) :
    g.edist (p 0) (p N) ≤ ENNReal.ofReal (∑ i ∈ Finset.range N, l i) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  induction N with
  | zero => simp [PoincareConjecture.RiemannianMetric.edist, Manifold.riemannianEDist_self]
  | succ N ih =>
    have h := Manifold.riemannianEDist_triangle (I := 𝓡 n)
      (x := p 0) (y := p N) (z := p (N + 1))
    change g.edist (p 0) (p (N + 1)) ≤ g.edist (p 0) (p N) +
      g.edist (p N) (p (N + 1)) at h
    refine (h.trans (add_le_add (ih (fun i hi => hl i (Nat.lt_succ_of_lt hi))
      (fun i hi => hd i (Nat.lt_succ_of_lt hi))) (hd N (Nat.lt_succ_self N)))).trans_eq ?_
    rw [Finset.sum_range_succ, ENNReal.ofReal_add
      (Finset.sum_nonneg fun i hi => hl i (Nat.lt_succ_of_lt (Finset.mem_range.mp hi)))
      (hl N (Nat.lt_succ_self N))]

theorem sum_energy_ge_of_minimizing_endpoints
    (g : PoincareConjecture.RiemannianMetric n M) {N : ℕ} (τ : ℕ → ℝ)
    (γ : ℕ → ℝ → M) (p : ℕ → M) {C : ℝ} (hC : 0 < C)
    (hτ : ∀ i < N, τ i ≤ τ (i + 1))
    (hγ : ∀ i < N, ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ i) (Icc (τ i) (τ (i + 1))))
    (hcont : ∀ i < N, ContinuousOn (fun t =>
      g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1))
        (Icc (τ i) (τ (i + 1))))
    (hleft : ∀ i < N, γ i (τ i) = p i)
    (hright : ∀ i < N, γ i (τ (i + 1)) = p (i + 1))
    (hmin : g.edist (p 0) (p N) = ENNReal.ofReal ((τ N - τ 0) * C)) :
    (τ N - τ 0) * C ^ 2 ≤ ∑ i ∈ Finset.range N, ∫ t in (τ i)..(τ (i + 1)),
      (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2 := by
  let E : ℕ → ℝ := fun i => ∫ t in (τ i)..(τ (i + 1)),
    (g.tangentNorm (γ i t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (γ i) t 1)) ^ 2
  let l : ℕ → ℝ := fun i => (E i + (τ (i + 1) - τ i) * C ^ 2) / (2 * C)
  have hl : ∀ i < N, 0 ≤ l i := by
    intro i hi
    have hE : 0 ≤ E i := intervalIntegral.integral_nonneg (hτ i hi)
      (fun _ _ => sq_nonneg _)
    exact div_nonneg (add_nonneg hE (mul_nonneg (sub_nonneg.mpr (hτ i hi))
      (sq_nonneg C))) (by positivity)
  have hd : ∀ i < N, g.edist (p i) (p (i + 1)) ≤ ENNReal.ofReal (l i) := by
    intro i hi
    rw [← hleft i hi, ← hright i hi]
    exact g.edist_le_ofReal_energy_bound (hτ i hi) hC (hγ i hi) (hcont i hi)
  have h := edist_le_ofReal_sum g p l N hl hd
  rw [hmin, ENNReal.ofReal_le_ofReal_iff
    (Finset.sum_nonneg fun i hi => hl i (Finset.mem_range.mp hi))] at h
  have hsum : ∑ i ∈ Finset.range N, (τ (i + 1) - τ i) = τ N - τ 0 := by
    clear h hl hd hmin hright hleft hcont hγ hτ
    induction N with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  have heq : (∑ i ∈ Finset.range N, l i) =
      ((∑ i ∈ Finset.range N, E i) + (τ N - τ 0) * C ^ 2) / (2 * C) := by
    simp only [l, ← Finset.sum_div, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
  rw [heq] at h
  have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp h
  change (τ N - τ 0) * C ^ 2 ≤ ∑ i ∈ Finset.range N, E i
  nlinarith

end Poincare.VolumeComparison.Conjugate
