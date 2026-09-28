import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Energy.Caccioppoli
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.InteriorEstimates.Operators.Basic

noncomputable section

open Set MeasureTheory
open scoped ContDiff
open Poincare.Analysis.Elliptic.Iteration
open Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.NirenbergEuclidean

namespace Poincare.Analysis.Elliptic.InteriorEstimates

variable {d : ℕ} [NeZero d]
local notation "E" => EuclideanSpace ℝ (Fin d)

omit [NeZero d] in
theorem integral_drift_cutoff_eq {V : Set E} (hV : IsOpen V)
    {c η u : E → ℝ} (hc : ContDiff ℝ ∞ c) (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport η) (hηV : tsupport η ⊆ V)
    (hu : ContDiff ℝ ∞ u) (i : Fin d) :
    (∫ x in V, c x * partialDeriv i u x * ((η x * η x) * u x)) =
      -(1 / 2 : ℝ) * ∫ x in V, u x ^ 2 *
        partialDeriv i (fun y => c y * (η y * η y)) x := by
  let ψ : E → ℝ := fun x => c x * (η x * η x)
  have hψ : ContDiff ℝ ∞ ψ := hc.mul (hη.mul hη)
  have hψc : HasCompactSupport ψ := hηc.mul_right.mul_left
  have hψV : tsupport ψ ⊆ V :=
    (tsupport_mul_subset_right.trans tsupport_mul_subset_left).trans hηV
  have hweak := HasWeakPartialDeriv.of_contDiff (i := i) hV
    ((hu.mul hu).of_le (by simp)) ψ hψ hψc hψV
  have hprod (x : E) : partialDeriv i (fun y => u y * u y) x =
      2 * u x * partialDeriv i u x := by
    change (fderiv ℝ (fun y => u y * u y) x) (EuclideanSpace.single i 1) = _
    rw [fderiv_fun_mul (hu.differentiable (by simp) x)
      (hu.differentiable (by simp) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, partialDeriv]
    ring
  change (∫ x in V, (u x * u x) * partialDeriv i ψ x) =
    -(∫ x in V, partialDeriv i (fun y => u y * u y) x * ψ x) at hweak
  simp_rw [hprod] at hweak
  have hid : (∫ x in V, 2 * u x * partialDeriv i u x * ψ x) =
      2 * ∫ x in V, c x * partialDeriv i u x * ((η x * η x) * u x) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with x
    dsimp [ψ]
    ring
  rw [hid] at hweak
  have hleft : (∫ x in V, (u x * u x) * partialDeriv i ψ x) =
      ∫ x in V, u x ^ 2 * partialDeriv i (fun y => c y * (η y * η y)) x := by
    simp only [pow_two, ψ]
  rw [hleft] at hweak
  linarith

theorem exists_gradient_integral_le_with_drift
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W) (hWV : W ⊆ V)
    (c : Fin d → E → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i))
    {η : E → ℝ} (hη : ContDiff ℝ ∞ η) (hηc : HasCompactSupport η)
    (hηV : tsupport η ⊆ V) (hηrange : range η ⊆ Icc (0 : ℝ) 1)
    (hηone : ∀ x ∈ W, η x = 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) =
          ∫ x in V, (f x + ∑ i, c i x * partialDeriv i u x) * φ x) →
      (∫ x in W, ∑ i : Fin d, (partialDeriv i u x) ^ 2) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  let z : E → ℝ := fun x => B.principalIntegrand η η x -
    (1 / 2 : ℝ) * ∑ i, partialDeriv i (fun y => c i y * (η y * η y)) x
  have hz : Continuous z :=
    (B.continuous_principalIntegrand (hη.of_le (by simp)) (hη.of_le (by simp))).sub
      (continuous_const.mul (continuous_finsetSum _ fun i _ =>
        (contDiff_partial ((hc i).mul (hη.mul hη)) i).continuous))
  have hsumc : HasCompactSupport (fun x =>
      ∑ i, partialDeriv i (fun y => c i y * (η y * η y)) x) := by
    apply HasCompactSupport.of_support_subset_isCompact hηc
    intro x hx
    by_contra hn
    apply hx
    apply Finset.sum_eq_zero
    intro i hi
    have hnot : x ∉ tsupport (fun y => c i y * (η y * η y)) :=
      fun hm => hn ((tsupport_mul_subset_right.trans tsupport_mul_subset_left) hm)
    simp [partialDeriv, fderiv_of_notMem_tsupport ℝ hnot]
  have hzc : HasCompactSupport z :=
    (principal_hasCompactSupport_right B η hηc).sub hsumc.mul_left
  obtain ⟨Q, hQ, hQbound⟩ :=
    Poincare.Analysis.Sobolev.NirenbergCrossBoundsNonSmooth.exists_bound_of_continuous_compactSupport
      hz hzc
  refine ⟨(1 + Q) / B.lam, div_nonneg (by positivity) B.lam_nonneg, ?_⟩
  intro u f hu hum hfm heq
  let v : E → ℝ := fun x => η x * u x
  let φ : E → ℝ := fun x => (η x * η x) * u x
  have hφ : ContDiff ℝ ∞ φ := (hη.mul hη).mul hu
  have hφc : HasCompactSupport φ := hηc.mul_right.mul_right
  have hφV : tsupport φ ⊆ V :=
    (tsupport_mul_subset_left.trans tsupport_mul_subset_left).trans hηV
  have htest : Integrable (B.principalIntegrand u φ) volume :=
    (B.continuous_principalIntegrand (hu.of_le (by simp))
      (hφ.of_le (by simp))).integrable_of_hasCompactSupport
        (principal_hasCompactSupport_right B u hφc)
  have hcut : Integrable (fun x => u x ^ 2 * B.principalIntegrand η η x) volume :=
    ((hu.continuous.pow 2).mul
      (B.continuous_principalIntegrand (hη.of_le (by simp))
        (hη.of_le (by simp)))).integrable_of_hasCompactSupport
          (principal_hasCompactSupport_right B η hηc).mul_left
  have hfφ : Integrable (fun x => f x * φ x) (volume.restrict V) :=
    hfm.integrable_mul ((hφ.continuous.memLp_of_hasCompactSupport
      (p := 2) hφc).restrict V)
  have hdi (i : Fin d) : Integrable (fun x => c i x * partialDeriv i u x * φ x)
      (volume.restrict V) :=
    (((hc i).continuous.mul (contDiff_partial hu i).continuous).mul
      hφ.continuous).integrable_of_hasCompactSupport hφc.mul_left |>.restrict
  have hzi (i : Fin d) : Integrable (fun x => u x ^ 2 *
      partialDeriv i (fun y => c i y * (η y * η y)) x) (volume.restrict V) :=
    ((hu.continuous.pow 2).mul
      (contDiff_partial ((hc i).mul (hη.mul hη)) i).continuous).integrable_of_hasCompactSupport
        (hasCompactSupport_partial (hηc.mul_right.mul_left) i).mul_left |>.restrict
  have huz : Integrable (fun x => u x ^ 2 * z x) (volume.restrict V) :=
    ((hu.continuous.pow 2).mul hz).integrable_of_hasCompactSupport hzc.mul_left |>.restrict
  have hid : (∫ x in V, B.principalIntegrand v v x) =
      (∫ x in V, f x * φ x) + ∫ x in V, u x ^ 2 * z x := by
    have htestEq := heq φ hφ hφc hφV
    simp_rw [add_mul, Finset.sum_mul] at htestEq
    rw [integral_add hfφ (integrable_finsetSum _ (fun i _ => hdi i)),
      integral_finsetSum _ (fun i _ => hdi i)] at htestEq
    dsimp only [φ] at htestEq
    simp_rw [integral_drift_cutoff_eq hV (hc _) hη hηc hηV hu] at htestEq
    have hident : (∫ x in V, B.principalIntegrand v v x) =
        (∫ x in V, B.principalIntegrand u φ x) +
          ∫ x in V, u x ^ 2 * B.principalIntegrand η η x := by
      simp_rw [show ∀ x, B.principalIntegrand v v x =
          B.principalIntegrand u φ x + u x ^ 2 * B.principalIntegrand η η x from
        principal_cutoff_identity B hη hu]
      exact integral_add htest.restrict hcut.restrict
    rw [hident, htestEq]
    have hzint : (∫ x in V, u x ^ 2 * z x) =
        (∫ x in V, u x ^ 2 * B.principalIntegrand η η x) -
          (1 / 2 : ℝ) * ∑ i, ∫ x in V, u x ^ 2 *
            partialDeriv i (fun y => c i y * (η y * η y)) x := by
      simp only [z, mul_sub, mul_left_comm (u _ ^ 2) (1 / 2 : ℝ), Finset.mul_sum]
      rw [integral_sub hcut.restrict
        (integrable_finsetSum _ (fun i _ => (hzi i).const_mul (1 / 2 : ℝ))),
        integral_finsetSum _ (fun i _ => (hzi i).const_mul (1 / 2 : ℝ))]
      simp_rw [integral_const_mul]
    rw [hzint, ← Finset.mul_sum]
    ring
  have hupper : (∫ x in V, B.principalIntegrand v v x) ≤
      (1 + Q) * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
    rw [hid, ← integral_add hfφ huz,
      ← integral_add hum.integrable_sq hfm.integrable_sq, ← integral_const_mul]
    apply integral_mono (hfφ.add huz)
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
    have hzbound : u x ^ 2 * z x ≤ u x ^ 2 * Q :=
      mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hQbound x)) (sq_nonneg _)
    have hsource := (le_abs_self (f x * φ x)).trans (habs.trans hfu)
    dsimp only [Pi.add_apply]
    nlinarith [mul_nonneg hQ (sq_nonneg (f x))]
  have hlow := gradient_integral_le_cutoff_principal_integral
    B hV hVΩ hW hWV hη hηc hηone hu
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ B.hlam_pos).mpr
  simpa only [mul_comm B.lam, partialDeriv] using hlow.trans hupper

theorem exists_gradient_integral_le_with_drift_on_nested_sets
    {Ω V W : Set E} (B : SmoothEllipticBilinearForm d Ω)
    (hV : IsOpen V) (hVΩ : V ⊆ Ω) (hW : IsOpen W)
    (hWc : IsCompact (closure W)) (hWV : closure W ⊆ V)
    (c : Fin d → E → ℝ) (hc : ∀ i, ContDiff ℝ ∞ (c i)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u f : E → ℝ}, ContDiff ℝ ∞ u →
      MemLp u 2 (volume.restrict V) → MemLp f 2 (volume.restrict V) →
      (∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ V →
        (∫ x in V, B.principalIntegrand u φ x) =
          ∫ x in V, (f x + ∑ i, c i x * partialDeriv i u x) * φ x) →
      (∫ x in W, ∑ i : Fin d, (partialDeriv i u x) ^ 2) ≤
        C * ((∫ x in V, u x ^ 2) + ∫ x in V, f x ^ 2) := by
  obtain ⟨η, hη, hηc, hηrange, hηone, hηV⟩ :=
    SmoothEllipticBilinearForm.exists_cutoff hWc hV hWV
  exact exists_gradient_integral_le_with_drift B hV hVΩ hW
    (subset_closure.trans hWV) c hc hη hηc hηV hηrange
    (fun x hx => hηone x (subset_closure hx))

end Poincare.Analysis.Elliptic.InteriorEstimates
