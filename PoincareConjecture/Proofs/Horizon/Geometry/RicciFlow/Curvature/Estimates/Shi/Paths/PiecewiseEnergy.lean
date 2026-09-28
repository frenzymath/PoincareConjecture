import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic












set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Topology Manifold ContDiff Bundle ENNReal BigOperators

namespace PoincareConjecture.RicciFlowAnalysis

private theorem sq_sum_integral_le_sum_integral_sq
    (N : ℕ) (τ : ℕ → ℝ) (v : ℕ → ℝ → ℝ)
    (hmesh : ∀ i, i < N → τ i ≤ τ (i + 1))
    (hspan : τ N - τ 0 = 1)
    (hv : ∀ i, i < N → ContinuousOn (v i) (Icc (τ i) (τ (i + 1)))) :
    (∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), v i t) ^ 2 ≤
      ∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), (v i t) ^ 2 := by
  let L : ℝ := ∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), v i t
  have hvariance (i : ℕ) (hi : i < N) :
      (∫ t in τ i..τ (i + 1), (v i t - L) ^ 2) =
        (∫ t in τ i..τ (i + 1), (v i t) ^ 2) -
          (2 * L) * (∫ t in τ i..τ (i + 1), v i t) +
          (τ (i + 1) - τ i) * L ^ 2 := by
    have hiSq : IntervalIntegrable (fun t => (v i t) ^ 2) volume
        (τ i) (τ (i + 1)) :=
      ContinuousOn.intervalIntegrable_of_Icc (hmesh i hi) ((hv i hi).pow 2)
    have hiMul : IntervalIntegrable (fun t => (2 * L) * v i t) volume
        (τ i) (τ (i + 1)) :=
      ContinuousOn.intervalIntegrable_of_Icc (hmesh i hi)
        (continuousOn_const.mul (hv i hi))
    calc
      _ = ∫ t in τ i..τ (i + 1),
          (v i t) ^ 2 - (2 * L) * v i t + L ^ 2 :=
        intervalIntegral.integral_congr (fun t _ => by ring)
      _ = _ := by
        rw [intervalIntegral.integral_add (hiSq.sub hiMul)
          (continuous_const.intervalIntegrable _ _)]
        rw [intervalIntegral.integral_sub hiSq hiMul,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
  have hnonneg : 0 ≤ ∑ i ∈ Finset.range N,
      ((∫ t in τ i..τ (i + 1), (v i t) ^ 2) -
        (2 * L) * (∫ t in τ i..τ (i + 1), v i t) +
        (τ (i + 1) - τ i) * L ^ 2) := by
    apply Finset.sum_nonneg
    intro i hi
    rw [← hvariance i (Finset.mem_range.mp hi)]
    exact intervalIntegral.integral_nonneg (hmesh i (Finset.mem_range.mp hi))
      (fun t _ => sq_nonneg _)
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul, Finset.sum_range_sub, hspan] at hnonneg
  change 0 ≤ (∑ i ∈ Finset.range N, ∫ t in τ i..τ (i + 1), (v i t) ^ 2) -
    (2 * L) * L + 1 * L ^ 2 at hnonneg
  change L ^ 2 ≤ _
  nlinarith only [hnonneg]

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


noncomputable def segmentPathSpeed (g : RiemannianMetric n M)
    (γ : ℝ → M) (a b t : ℝ) : ℝ :=
  g.tangentNorm (γ t) (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)


noncomputable def segmentPathEnergy (g : RiemannianMetric n M)
    (γ : ℝ → M) (a b : ℝ) : ℝ :=
  ∫ t in a..b, g.inner (γ t)
    (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)
    (mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1)

theorem segmentPathSpeed_nonneg (g : RiemannianMetric n M)
    (γ : ℝ → M) (a b t : ℝ) : 0 ≤ segmentPathSpeed g γ a b t :=
  Real.sqrt_nonneg _

theorem segmentPathEnergy_eq_integral_segmentPathSpeed_sq
    (g : RiemannianMetric n M) (γ : ℝ → M) (a b : ℝ) :
    segmentPathEnergy g γ a b =
      ∫ t in a..b, (segmentPathSpeed g γ a b t) ^ 2 := by
  apply intervalIntegral.integral_congr
  intro t _
  apply (Real.sq_sqrt ?_).symm
  by_cases hv : mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1 = 0
  · simp [hv]
  · exact (g.pos (γ t) _ hv).le

theorem continuousOn_segmentPathSpeed (g : RiemannianMetric n M)
    {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) (hab : a < b) :
    ContinuousOn (segmentPathSpeed g γ a b) (Icc a b) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hinput : Continuous
      (fun t : ℝ => (⟨t, (1 : ℝ)⟩ : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
    (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
      (continuous_id.prodMk continuous_const)
  have hvelocity : ContinuousOn (fun t : ℝ =>
      (⟨γ t, mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1⟩ :
        TangentBundle (𝓡 n) M)) (Icc a b) :=
    (hγ.continuousOn_tangentMapWithin le_rfl
      (uniqueDiffOn_Icc hab).uniqueMDiffOn).comp
        hinput.continuousOn (fun t ht => ht)
  exact (hvelocity.inner_bundle hvelocity).sqrt

theorem pathELength_eq_ofReal_integral_segmentPathSpeed
    (g : RiemannianMetric n M) {γ : ℝ → M} {a b : ℝ}
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 γ (Icc a b)) (hab : a < b) :
    g.pathELength γ a b =
      ENNReal.ofReal (∫ t in a..b, segmentPathSpeed g γ a b t) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  change Manifold.pathELength (𝓡 n) γ a b = _
  rw [Manifold.pathELength_eq_lintegral_mfderivWithin_Icc]
  have hnorm (t : ℝ) : ‖mfderivWithin 𝓘(ℝ, ℝ) (𝓡 n) γ (Icc a b) t 1‖ₑ =
      ENNReal.ofReal (segmentPathSpeed g γ a b t) := by
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  simp_rw [hnorm]
  rw [intervalIntegral.integral_of_le hab.le, ← integral_Icc_eq_integral_Ioc]
  exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
    (continuousOn_segmentPathSpeed g hγ hab).integrableOn_Icc
    (Eventually.of_forall (segmentPathSpeed_nonneg g γ a b))).symm



theorem edist_le_sqrt_sum_segmentPathEnergy
    (g : RiemannianMetric n M) (N : ℕ) (τ : ℕ → ℝ)
    (γ : ℕ → ℝ → M) (x : ℕ → M)
    (hmesh : ∀ i, i < N → τ i < τ (i + 1))
    (hspan : τ N - τ 0 = 1)
    (hγ : ∀ i, i < N →
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) 1 (γ i) (Icc (τ i) (τ (i + 1))))
    (hleft : ∀ i, i < N → γ i (τ i) = x i)
    (hright : ∀ i, i < N → γ i (τ (i + 1)) = x (i + 1)) :
    g.edist (x 0) (x N) ≤ ENNReal.ofReal (Real.sqrt
      (∑ i ∈ Finset.range N, segmentPathEnergy g (γ i) (τ i) (τ (i + 1)))) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let ℓ : ℕ → ℝ := fun i =>
    ∫ t in τ i..τ (i + 1), segmentPathSpeed g (γ i) (τ i) (τ (i + 1)) t
  have hℓ0 (i : ℕ) (hi : i < N) : 0 ≤ ℓ i :=
    intervalIntegral.integral_nonneg (hmesh i hi).le
      (fun t _ => segmentPathSpeed_nonneg g (γ i) (τ i) (τ (i + 1)) t)
  have hlength (i : ℕ) (hi : i < N) :
      g.pathELength (γ i) (τ i) (τ (i + 1)) = ENNReal.ofReal (ℓ i) :=
    pathELength_eq_ofReal_integral_segmentPathSpeed g (hγ i hi) (hmesh i hi)
  have hpath (i : ℕ) (hi : i < N) :
      g.edist (x i) (x (i + 1)) ≤ g.pathELength (γ i) (τ i) (τ (i + 1)) := by
    change Manifold.riemannianEDist (𝓡 n) (x i) (x (i + 1)) ≤
      Manifold.pathELength (𝓡 n) (γ i) (τ i) (τ (i + 1))
    exact Manifold.riemannianEDist_le_pathELength
      (hγ i hi) (hleft i hi) (hright i hi) (hmesh i hi).le
  have hchain : ∀ k, k ≤ N → g.edist (x 0) (x k) ≤
      ∑ i ∈ Finset.range k, g.pathELength (γ i) (τ i) (τ (i + 1)) := by
    intro k
    induction k with
    | zero =>
        intro _
        change Manifold.riemannianEDist (𝓡 n) (x 0) (x 0) ≤ _
        simp only [Manifold.riemannianEDist_self, Finset.range_zero, Finset.sum_empty,
          le_refl]
    | succ k ih =>
        intro hk
        have hki : k < N := lt_of_lt_of_le (Nat.lt_succ_self k) hk
        have htri : g.edist (x 0) (x (k + 1)) ≤
            g.edist (x 0) (x k) + g.edist (x k) (x (k + 1)) := by
          change Manifold.riemannianEDist (𝓡 n) (x 0) (x (k + 1)) ≤
            Manifold.riemannianEDist (𝓡 n) (x 0) (x k) +
              Manifold.riemannianEDist (𝓡 n) (x k) (x (k + 1))
          exact Manifold.riemannianEDist_triangle
        simpa only [Finset.sum_range_succ] using
          htri.trans (add_le_add (ih hki.le) (hpath k hki))
  have hsq : (∑ i ∈ Finset.range N, ℓ i) ^ 2 ≤
      ∑ i ∈ Finset.range N, segmentPathEnergy g (γ i) (τ i) (τ (i + 1)) := by
    simp_rw [segmentPathEnergy_eq_integral_segmentPathSpeed_sq]
    exact sq_sum_integral_le_sum_integral_sq N τ
      (fun i => segmentPathSpeed g (γ i) (τ i) (τ (i + 1)))
      (fun i hi => (hmesh i hi).le) hspan
      (fun i hi => continuousOn_segmentPathSpeed g (hγ i hi) (hmesh i hi))
  calc
    g.edist (x 0) (x N) ≤
        ∑ i ∈ Finset.range N, g.pathELength (γ i) (τ i) (τ (i + 1)) :=
      hchain N le_rfl
    _ = ∑ i ∈ Finset.range N, ENNReal.ofReal (ℓ i) :=
      Finset.sum_congr rfl (fun i hi => hlength i (Finset.mem_range.mp hi))
    _ = ENNReal.ofReal (∑ i ∈ Finset.range N, ℓ i) :=
      (ENNReal.ofReal_sum_of_nonneg
        (fun i hi => hℓ0 i (Finset.mem_range.mp hi))).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (Real.le_sqrt_of_sq_le hsq)

end PoincareConjecture.RicciFlowAnalysis
