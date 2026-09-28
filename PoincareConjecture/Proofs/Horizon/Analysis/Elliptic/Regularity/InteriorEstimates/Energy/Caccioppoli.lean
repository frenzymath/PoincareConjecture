import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.CrossTerms.Principal









noncomputable section

open MeasureTheory Set
open scoped ContDiff
open Poincare.Analysis.Sobolev.NirenbergEuclidean
open Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

theorem principal_cutoff_identity {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) {η u : E → ℝ}
    (hη : ContDiff ℝ ∞ η) (hu : ContDiff ℝ ∞ u) (x : E) :
    B.principalIntegrand (fun y => η y * u y) (fun y => η y * u y) x =
      B.principalIntegrand u (fun y => (η y * η y) * u y) x +
        u x ^ 2 * B.principalIntegrand η η x := by
  have hηd := (hη.differentiable (by simp)).differentiableAt (x := x)
  have hud := (hu.differentiable (by simp)).differentiableAt (x := x)
  have htest : fderiv ℝ (fun y => (η y * η y) * u y) x =
      (η x * η x) • fderiv ℝ u x +
        u x • (η x • fderiv ℝ η x + η x • fderiv ℝ η x) := by
    rw [fderiv_fun_mul (c := fun y => η y * η y) (hηd.mul hηd) hud,
      fderiv_fun_mul hηd hηd]
  have hsym := B.principalIntegrand_symm u η x
  calc
    _ = B.principalIntegrand u (fun y => (η y * η y) * u y) x +
        u x ^ 2 * B.principalIntegrand η η x +
          (η x * u x) * (B.principalIntegrand η u x - B.principalIntegrand u η x) := by
      unfold SmoothEllipticBilinearForm.principalIntegrand
      simp only [fderiv_fun_mul hηd hud, htest, add_apply, smul_apply, smul_eq_mul,
        ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hsym, sub_self, mul_zero, add_zero]

theorem principal_hasCompactSupport_right {Ω : Set E}
    (B : SmoothEllipticBilinearForm d Ω) (u : E → ℝ)
    {v : E → ℝ} (hv : HasCompactSupport v) :
    HasCompactSupport (B.principalIntegrand u v) := by
  apply HasCompactSupport.of_support_subset_isCompact hv
  intro x hx
  by_contra hnot
  apply hx
  simp [SmoothEllipticBilinearForm.principalIntegrand,
    fderiv_of_notMem_tsupport ℝ hnot]


theorem gradient_integral_le_cutoff_principal_integral
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W) (hWV : W ⊆ V)
    {η u : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηone : ∀ x ∈ W, η x = 1) (hu : ContDiff ℝ ∞ u) :
    B.lam * (∫ x in W,
      ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
      ∫ x in V, B.principalIntegrand (fun y => η y * u y) (fun y => η y * u y) x := by
  let v : E → ℝ := fun x => η x * u x
  have hv : ContDiff ℝ ∞ v := hη.mul hu
  have hvc : HasCompactSupport v := hηc.mul_right
  have henergy : Integrable (B.principalIntegrand v v) volume :=
    (B.continuous_principalIntegrand (hv.of_le (by simp))
      (hv.of_le (by simp))).integrable_of_hasCompactSupport
        (principal_hasCompactSupport_right B v hvc)
  have hgrad : Integrable (fun x =>
      ∑ i : Fin d, (fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    have hdm : MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
        2 (volume : Measure E) :=
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hvc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1))
    exact hdm.integrable_sq
  have hderiv (x : E) (hx : x ∈ W) : fderiv ℝ v x = fderiv ℝ u x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hW.mem_nhds hx] with y hy
    simp [v, hηone y hy]
  have heqgrad : (∫ x in W,
      ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ x in W, ∑ i : Fin d, (fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2 := by
    apply setIntegral_congr_fun hW.measurableSet
    intro x hx
    dsimp only
    rw [hderiv x hx]
  rw [heqgrad, ← integral_const_mul]
  apply (setIntegral_mono_on (hgrad.restrict.const_mul B.lam) henergy.restrict
    hW.measurableSet (fun x hx => ?_)).trans
  · exact setIntegral_mono_set henergy.restrict
      ((ae_restrict_mem hV.measurableSet).mono fun x hx =>
        (mul_nonneg B.lam_nonneg (sq_nonneg _)).trans
          (B.principalIntegrand_self_ge v (hVΩ hx)))
      (Filter.Eventually.of_forall hWV)
  · simpa only [SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum] using
      B.principalIntegrand_self_ge v (hVΩ (hWV hx))



theorem exists_gradient_integral_le_of_weakEquation
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W) (hWV : W ⊆ V)
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    (hηone : ∀ x ∈ W, η x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨Q, hQ, hQbound⟩ := exists_bound_of_continuous_compactSupport
    (B.continuous_principalIntegrand (hη.of_le (by simp)) (hη.of_le (by simp)))
    (principal_hasCompactSupport_right B η hηc)
  refine ⟨(1 + Q) / B.lam, div_nonneg (by positivity) B.lam_nonneg, ?_⟩
  intro u f hu hum hfm heq
  let v : E → ℝ := fun x => η x * u x
  let φ : E → ℝ := fun x => (η x * η x) * u x
  have hv : ContDiff ℝ ∞ v := hη.mul hu
  have hφ : ContDiff ℝ ∞ φ := (hη.mul hη).mul hu
  have hvc : HasCompactSupport v := hηc.mul_right
  have hφc : HasCompactSupport φ := hηc.mul_right.mul_right
  have hφV : tsupport φ ⊆ V :=
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hηV
  have henergy : Integrable (B.principalIntegrand v v) volume :=
    (B.continuous_principalIntegrand (hv.of_le (by simp)) (hv.of_le (by simp))).integrable_of_hasCompactSupport
      (principal_hasCompactSupport_right B v hvc)
  have htest : Integrable (B.principalIntegrand u φ) volume :=
    (B.continuous_principalIntegrand (hu.of_le (by simp)) (hφ.of_le (by simp))).integrable_of_hasCompactSupport
      (principal_hasCompactSupport_right B u hφc)
  have hcut : Integrable (fun x => u x ^ 2 * B.principalIntegrand η η x) volume :=
    ((hu.continuous.pow 2).mul
      (B.continuous_principalIntegrand (hη.of_le (by simp)) (hη.of_le (by simp)))).integrable_of_hasCompactSupport
        (principal_hasCompactSupport_right B η hηc).mul_left
  have hfφ : Integrable (fun x => f x * φ x) (volume.restrict V) :=
    hfm.integrable_mul ((hφ.continuous.memLp_of_hasCompactSupport
      (p := 2) hφc).restrict V)
  have hupper : (∫ x in V, B.principalIntegrand v v x) ≤
      (1 + Q) * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
    have hid := heq φ hφ hφc hφV
    have hident : (∫ x in V, B.principalIntegrand v v x) =
        (∫ x in V, f x * φ x) + ∫ x in V, u x ^ 2 * B.principalIntegrand η η x := by
      simp_rw [show ∀ x, B.principalIntegrand v v x =
          B.principalIntegrand u φ x + u x ^ 2 * B.principalIntegrand η η x from
        principal_cutoff_identity B hη hu]
      rw [integral_add htest.restrict hcut.restrict, hid]
    rw [hident, ← integral_add hfφ hcut.restrict,
      ← integral_add hum.integrable_sq hfm.integrable_sq, ← integral_const_mul]
    apply integral_mono (hfφ.add hcut.restrict)
      ((hum.integrable_sq.add hfm.integrable_sq).const_mul (1 + Q))
    intro x
    have hηx := hηrange (mem_range_self x)
    have hηsq : (η x) ^ 2 ≤ 1 := by nlinarith [hηx.1, hηx.2]
    have habs : |f x * φ x| ≤ |f x * u x| := by
      dsimp only [φ]
      rw [show f x * (η x * η x * u x) = (η x)^2 * (f x * u x) by ring,
        abs_mul, abs_of_nonneg (sq_nonneg _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hηsq
    have hfu : |f x * u x| ≤ (f x)^2 + (u x)^2 := by
      rw [abs_mul]
      nlinarith [sq_nonneg (|f x| - |u x|), sq_abs (f x), sq_abs (u x)]
    have hcutbound : u x ^ 2 * B.principalIntegrand η η x ≤ u x ^ 2 * Q :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hQbound x)) (sq_nonneg _)
    have hsource := (le_abs_self (f x * φ x)).trans (habs.trans hfu)
    dsimp only [Pi.add_apply]
    nlinarith [mul_nonneg hQ (sq_nonneg (f x))]
  have hgrad : Integrable (fun x =>
      ∑ i : Fin d, (fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2) volume := by
    apply integrable_finsetSum
    intro i hi
    have hdc := hvc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hdm : MemLp (fun x => fderiv ℝ v x (EuclideanSpace.single i 1))
        2 (volume : Measure E) :=
      ((hv.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport hdc
    exact hdm.integrable_sq
  have hderiv (x : E) (hx : x ∈ W) : fderiv ℝ v x = fderiv ℝ u x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [hW.mem_nhds hx] with y hy
    simp [v, hηone y hy]
  have hlow : B.lam * (∫ x in W,
      ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
      ∫ x in V, B.principalIntegrand v v x := by
    have heqgrad : (∫ x in W,
        ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) =
        ∫ x in W, ∑ i : Fin d, (fderiv ℝ v x (EuclideanSpace.single i 1)) ^ 2 := by
      apply setIntegral_congr_fun hW.measurableSet
      intro x hx
      dsimp only
      rw [hderiv x hx]
    rw [heqgrad, ← integral_const_mul]
    apply (setIntegral_mono_on (hgrad.restrict.const_mul B.lam) henergy.restrict
      hW.measurableSet (fun x hx => ?_)).trans
    · exact setIntegral_mono_set henergy.restrict
        ((ae_restrict_mem hV.measurableSet).mono fun x hx =>
          (mul_nonneg B.lam_nonneg (sq_nonneg _)).trans
            (B.principalIntegrand_self_ge v (hVΩ hx)))
        (Filter.Eventually.of_forall hWV)
    · simpa only [SmoothEllipticBilinearForm.gradientVec_norm_sq_eq_sum] using
        B.principalIntegrand_self_ge v (hVΩ (hWV hx))
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ B.hlam_pos).mpr
  simpa only [mul_comm B.lam] using hlow.trans hupper


theorem exists_gradient_integral_le_on_nested_sets
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) = ∫ x in V, f x * φ x) →
      (∫ x in W, ∑ i : Fin d, (fderiv ℝ u x (EuclideanSpace.single i 1)) ^ 2) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hWc hV hWV
  exact exists_gradient_integral_le_of_weakEquation B hV hVΩ hW
    (subset_closure.trans hWV) hη hηc hηV hηrange
    (fun x hx => hηone x (subset_closure hx))

end Poincare.Analysis.Elliptic.InteriorEstimates
