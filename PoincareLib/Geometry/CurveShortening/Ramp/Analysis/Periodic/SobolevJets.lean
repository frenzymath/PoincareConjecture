import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.FourierDecoder
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Actual spatial jets of periodic Sobolev reconstruction

The weighted Fourier decoder has actual derivatives through the order
allowed by the one-dimensional Sobolev bound. MT2007 Claim 19.1, p. 437;
contract review block 8 and `2026-09-21-periodic-sobolev-jets.md`.
M03's Euclidean Sobolev reconstruction is the reference pattern; here
Mathlib's Fourier modes and differentiation of series supply the proof.
-/

set_option autoImplicit false

open AddCircle
open scoped ENNReal

namespace PoincareMT.M63

/-- The actual multiplier for the j-th derivative of the order k
periodic reconstruction. MT2007 Claim 19.1, p. 437; the periodic
Sobolev-jet derivation, statement 1. -/
noncomputable def periodicSobolevMoment (L : ℝ) (k j : ℕ) (n : ℤ) : ℂ :=
  (Complex.I * (2 * Real.pi * (n : ℝ) / L : ℝ)) ^ j /
    (Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) : ℂ) ^ (k + 1)

variable {L : ℝ} [Fact (0 < L)]

/-- Every permitted derivative weight is bounded by the actual
square-summable H1 decay weight. MT2007 Claim 19.1, p. 437; the
periodic Sobolev-jet derivation, statement 2. -/
theorem periodicSobolevMoment_bound {k j : ℕ} (hj : j ≤ k) :
    (∀ n : ℤ, ‖periodicSobolevMoment L k j n‖ ≤
      1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)) ∧
    Memℓp (periodicSobolevMoment L k j) 2 := by
  have hb (n : ℤ) : ‖periodicSobolevMoment L k j n‖ ≤
      1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2) := by
    let ω : ℝ := 2 * Real.pi * (n : ℝ) / L
    let ρ : ℝ := Real.sqrt (1 + ω ^ 2)
    have hρ0 : 0 ≤ ρ := Real.sqrt_nonneg _
    have hρsq : ρ ^ 2 = 1 + ω ^ 2 := Real.sq_sqrt (by positivity)
    have hρ1 : 1 ≤ ρ := by nlinarith [sq_nonneg ω]
    have hρpos : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ1
    have hω : |ω| ≤ ρ := by nlinarith [sq_abs ω, abs_nonneg ω]
    have hpow : |ω| ^ j ≤ ρ ^ k :=
      (pow_le_pow_left₀ (abs_nonneg ω) hω j).trans (pow_le_pow_right₀ hρ1 hj)
    change ‖(Complex.I * (ω : ℂ)) ^ j / (ρ : ℂ) ^ (k + 1)‖ ≤ 1 / ρ
    simp only [norm_div, norm_pow, norm_mul, Complex.norm_I, one_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hρ0]
    calc
      |ω| ^ j / ρ ^ (k + 1) ≤ ρ ^ k / ρ ^ (k + 1) :=
        div_le_div_of_nonneg_right hpow (by positivity)
      _ = 1 / ρ := by rw [pow_succ]; field_simp
  exact ⟨hb, (memℓp_periodic_decayWeight (Fact.out : 0 < L)).mono hb⟩

/-- The actual bounded Fourier reconstruction of the j-th spatial
jet. MT2007 Claim 19.1, p. 437; the periodic Sobolev-jet derivation,
statement 3. Its weight is proved square summable. -/
noncomputable def periodicSobolevJet (k j : ℕ) (hj : j ≤ k) :
    lp (fun _ : ℤ => ℂ) 2 →L[ℂ] C(AddCircle L, ℂ) :=
  weightedFourier ⟨periodicSobolevMoment L k j, (periodicSobolevMoment_bound hj).2⟩

/-- The uniform jet bound has one constant for all j <= k. MT2007
Claim 19.1, p. 437; the periodic Sobolev-jet derivation, statement 4. -/
theorem norm_periodicSobolevJet_le (k j : ℕ) (hj : j ≤ k)
    (u : lp (fun _ : ℤ => ℂ) 2) :
    ‖periodicSobolevJet (L := L) k j hj u‖ ≤
      ‖(⟨(fun n : ℤ => 1 / Real.sqrt (1 + (2 * Real.pi * (n : ℝ) / L) ^ 2)),
        memℓp_periodic_decayWeight (Fact.out : 0 < L)⟩ : lp (fun _ : ℤ => ℝ) 2)‖ * ‖u‖ := by
  refine (norm_weightedFourier_le _ u).trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg u))
  apply lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0)
  intro n
  exact ((periodicSobolevMoment_bound hj).1 n).trans (Real.le_norm_self _)

/-- Consecutive reconstructed jets are actual derivatives of the
real lift. MT2007 Claim 19.1, p. 437; the periodic Sobolev-jet
derivation, statement 5. The strict order bound supplies a summable
derivative majorant. -/
theorem hasDerivAt_periodicSobolevJet {k j : ℕ} (hj : j < k)
    (u : lp (fun _ : ℤ => ℂ) 2) (x : ℝ) :
    HasDerivAt (fun y : ℝ => periodicSobolevJet (L := L) k j hj.le u (y : AddCircle L))
      (periodicSobolevJet (L := L) k (j + 1) hj u (x : AddCircle L)) x := by
  have hs (i : ℕ) (hi : i ≤ k) (y : ℝ) :
      HasSum (fun n : ℤ => periodicSobolevMoment L k i n * u n *
        fourier n (y : AddCircle L))
        (periodicSobolevJet (L := L) k i hi u (y : AddCircle L)) := by
    simpa only [periodicSobolevJet, ContinuousMap.evalCLM_apply,
      ContinuousMap.smul_apply, smul_eq_mul]
      using (ContinuousMap.evalCLM ℂ (y : AddCircle L)).hasSum
        (weightedFourier_hasSum
          ⟨periodicSobolevMoment L k i, (periodicSobolevMoment_bound hi).2⟩ u)
  have hm := (periodicSobolevMoment_bound (L := L) hj).2.holder 1 (lp.memℓp u)
    (fun _ : ℤ => ContinuousLinearMap.mul ℂ ℂ)
    (fun _ => ContinuousLinearMap.opNorm_mul_le ℂ ℂ)
  have hsum : Summable (fun n : ℤ => ‖periodicSobolevMoment L k (j + 1) n * u n‖) := by
    simpa using hm.summable
  have hd (n : ℤ) (y : ℝ) :
      HasDerivAt (fun z : ℝ => periodicSobolevMoment L k j n * u n *
        fourier n (z : AddCircle L))
        (periodicSobolevMoment L k (j + 1) n * u n * fourier n (y : AddCircle L)) y := by
    convert (hasDerivAt_fourier L n y).const_mul (periodicSobolevMoment L k j n * u n)
      using 1 <;> first | rfl | (simp only [periodicSobolevMoment, pow_succ,
        Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_ofNat,
        Complex.ofReal_intCast]; ring)
  have hbound (n : ℤ) (y : ℝ) :
      ‖periodicSobolevMoment L k (j + 1) n * u n * fourier n (y : AddCircle L)‖ ≤
        ‖periodicSobolevMoment L k (j + 1) n * u n‖ := by
    rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
  have hseries := hasDerivAt_tsum hsum hd hbound (hs j hj.le 0).summable x
  have heq : (fun y : ℝ => ∑' n : ℤ,
      periodicSobolevMoment L k j n * u n * fourier n (y : AddCircle L)) =
      (fun y : ℝ => periodicSobolevJet (L := L) k j hj.le u (y : AddCircle L)) :=
    funext fun y => (hs j hj.le y).tsum_eq
  rw [heq, (hs (j + 1) hj x).tsum_eq] at hseries
  exact hseries

/-- Periodic reconstruction has exactly the asserted finite spatial
regularity and actual iterated jets. MT2007 Claim 19.1, p. 437; the
periodic Sobolev-jet derivation, statement 6. -/
theorem periodicSobolevJet_regular (k : ℕ) (u : lp (fun _ : ℤ => ℂ) 2) :
    let U := fun x : ℝ => periodicSobolevJet (L := L) k 0 (Nat.zero_le k) u (x : AddCircle L)
    Function.Periodic U L ∧ ContDiff ℝ k U ∧
      ∀ j (hj : j ≤ k), iteratedDeriv j U =
        fun x : ℝ => periodicSobolevJet (L := L) k j hj u (x : AddCircle L) := by
  dsimp only
  have heq : ∀ j (hj : j ≤ k),
      iteratedDeriv j (fun x : ℝ =>
        periodicSobolevJet (L := L) k 0 (Nat.zero_le k) u (x : AddCircle L)) =
        fun x : ℝ => periodicSobolevJet (L := L) k j hj u (x : AddCircle L) := by
    intro j
    induction j with
    | zero => intro hj; rw [iteratedDeriv_zero]
    | succ j ih =>
        intro hj
        have hj' : j < k := Nat.lt_of_succ_le hj
        rw [iteratedDeriv_succ, ih hj'.le]
        funext x
        exact (hasDerivAt_periodicSobolevJet hj' u x).deriv
  refine ⟨?_, contDiff_nat_iff_iteratedDeriv.mpr ⟨?_, ?_⟩, heq⟩
  · intro x
    dsimp only
    rw [coe_add_period]
  · intro j hj
    rw [heq j hj]
    exact (periodicSobolevJet (L := L) k j hj u).continuous.comp
      (AddCircle.continuous_mk' L)
  · intro j hj
    rw [heq j hj.le]
    exact fun x => (hasDerivAt_periodicSobolevJet hj u x).differentiableAt

end PoincareMT.M63
