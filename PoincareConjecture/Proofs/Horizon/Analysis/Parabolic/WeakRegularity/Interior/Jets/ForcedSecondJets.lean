




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.ForcedHessianEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.L2DerivativeLimit
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakConvolution










open Set MeasureTheory Filter Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

local instance {n : ℕ} : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem exists_local_forced_weak_second_jets
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ} (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    {g : Fin n → Spacetime n → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hforce : ∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ U → (∫ y, u y * C.adjoint φ y) = ∫ y, φ y * f y)
    (hweak : ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ →
      HasCompactSupport φ → tsupport φ ⊆ U →
      (∫ y in U, φ y * g i y) = -(∫ y in U, spatialDeriv i φ y * u y))
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      ∃ (T : Spacetime n → ℝ) (H : Fin n → Fin n → Spacetime n → ℝ),
        MemLp T 2 volume ∧ (∀ i j, MemLp (H i j) 2 volume) ∧
        (∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * g i y) =
            -(∫ y in ball z r, spatialDeriv i φ y * u y)) ∧
        (∀ φ : Spacetime n → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * T y) =
            -(∫ y in ball z r, timeDeriv φ y * u y)) ∧
        (∀ i j (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * H i j y) =
            -(∫ y in ball z r, spatialDeriv i φ y * g j y)) := by
  let ρb : ContDiffBump (0 : Spacetime n) :=
    { rIn := 1, rOut := 2, rIn_pos := by norm_num, rIn_lt_rOut := by norm_num }
  let ρ : Spacetime n → ℝ := ρb.normed volume
  have hρ : ContDiff ℝ ∞ ρ := ρb.contDiff_normed
  have hρc : HasCompactSupport ρ := ρb.hasCompactSupport_normed
  have hmass : (∫ y, ρ y) = 1 := ρb.integral_normed
  obtain ⟨s, hs, hsU, ε, B, hε, hB, henergy⟩ :=
    exists_uniform_forced_mollified_second_energy hU hC hprincipalc hdriftc hzerothc
      hu hf hg hforce hweak hz hκ hEll hρ hρc
  obtain ⟨δ, hδ, hsupport⟩ := exists_uniform_translated_rescaledKernel_support_subset
    (isCompact_closedBall z s) hU hsU hρc
  let r : ℕ → ℝ := fun m => min ε δ / ((m : ℝ) + 1)
  have hr (m : ℕ) : 0 < r m := by dsimp only [r]; positivity
  have hrsmall (m : ℕ) : r m ≤ min ε δ :=
    div_le_self (lt_min hε hδ).le (by have := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := min ε δ)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [r, div_eq_mul_inv, one_mul, mul_zero] using ht
  have hη (m : ℕ) : ContDiff ℝ ∞ (rescaledKernel ρ (r m)) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
  have hηc (m : ℕ) : HasCompactSupport (rescaledKernel ρ (r m)) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
  have hfirst (m : ℕ) (j : Fin n) :
      EqOn (spatialDeriv j (mollifiedValue u ρ (r m)))
        (mollifiedValue (g j) ρ (r m)) (ball z s) := by
    intro y hy
    exact fderiv_lebesgueConvolution_eq_weakDerivative hU
      ((hu.locallyIntegrable (by norm_num)).locallyIntegrableOn U)
      (((hg j).locallyIntegrable (by norm_num)).locallyIntegrableOn U)
      (hweak j) (hη m) (hηc m)
      (hsupport (r m) (hr m) ((hrsmall m).trans (min_le_right _ _))
        y (ball_subset_closedBall hy))
  have hsecond (m : ℕ) (i j : Fin n) {y : Spacetime n} (hy : y ∈ ball z s) :
      spatialDeriv i (mollifiedValue (g j) ρ (r m)) y =
        spatialSecond i j (mollifiedValue u ρ (r m)) y := by
    exact congrArg (fun A : Spacetime n →L[ℝ] ℝ => A (spatialDirection i))
      ((hfirst m j).eventuallyEq_of_mem (isOpen_ball.mem_nhds hy)).fderiv_eq.symm
  have hdm (m : ℕ) (i j : Fin n) :
      MemLp (spatialDeriv i (mollifiedValue (g j) ρ (r m))) 2 volume :=
    memLp_fderiv_mollifiedValue (hg j) hρ hρc (hr m) (spatialDirection i)
  have hrow (j : Fin n) (m : ℕ) :
      (∫ y in ball z s, ∑ i, (spatialDeriv i (mollifiedValue (g j) ρ (r m)) y) ^ 2) ≤ B := by
    have hi := integrable_finsetSum Finset.univ
      (fun i _ => integrable_finsetSum Finset.univ (fun j _ => (hdm m i j).integrable_sq))
    have hrw := integrable_finsetSum Finset.univ (fun i _ => (hdm m i j).integrable_sq)
    have hb := integral_mono (μ := volume.restrict (ball z s))
      hrw.integrableOn hi.integrableOn (fun y =>
      Finset.sum_le_sum (fun i _ => Finset.single_le_sum
        (fun k _ => sq_nonneg (spatialDeriv i (mollifiedValue (g k) ρ (r m)) y))
        (Finset.mem_univ j)))
    have he : (∫ y in ball z s, ∑ i, ∑ j,
        (spatialDeriv i (mollifiedValue (g j) ρ (r m)) y) ^ 2) =
        ∫ y in ball z s, ∑ i, ∑ j, (spatialSecond i j (mollifiedValue u ρ (r m)) y) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
      simp_rw [hsecond m _ _ hy]
    rw [he] at hb
    have hB' := henergy (r m) (hr m) ((hrsmall m).trans (min_le_left _ _))
    have ht : 0 ≤ ∫ y in ball z s, (timeDeriv (mollifiedValue u ρ (r m)) y) ^ 2 :=
      integral_nonneg (fun _ => sq_nonneg _)
    linarith
  have htime (m : ℕ) : (∫ y in ball z s,
      ∑ _ : Unit, (fderiv ℝ (mollifiedValue u ρ (r m)) y (0, 1)) ^ 2) ≤ B := by
    have he := henergy (r m) (hr m) ((hrsmall m).trans (min_le_left _ _))
    have hh : 0 ≤ ∫ y in ball z s,
        ∑ i, ∑ j, (spatialSecond i j (mollifiedValue u ρ (r m)) y) ^ 2 :=
      integral_nonneg (fun _ => Finset.sum_nonneg (fun _ _ =>
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
    have ht : (∫ y in ball z s, (timeDeriv (mollifiedValue u ρ (r m)) y) ^ 2) ≤ B := by
      linarith only [he, hh]
    simpa only [Fintype.sum_unique, timeDeriv] using ht
  obtain ⟨T₀, hTweak, hTbound⟩ := exists_weak_derivatives_of_mollified_l2_energy
    isOpen_ball hu hρ hρc hmass hr hrlim (fun _ : Unit => (0, 1)) htime
  have hW (j : Fin n) : ∃ W : Fin n → Lp ℝ 2 (volume.restrict (ball z s)),
      (∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
        tsupport φ ⊆ ball z s → (∫ y in ball z s, φ y • W i y) =
          -(∫ y in ball z s, spatialDeriv i φ y • g j y)) ∧ (∑ i, ‖W i‖ ^ 2) ≤ B := by
    exact exists_weak_derivatives_of_mollified_l2_energy isOpen_ball (hg j)
      hρ hρc hmass hr hrlim spatialDirection (hrow j)
  choose W hWd hWb using hW
  let T : Spacetime n → ℝ := (ball z s).indicator (fun y => T₀ () y)
  let H : Fin n → Fin n → Spacetime n → ℝ :=
    fun i j => (ball z s).indicator (fun y => W j i y)
  have hTm : MemLp T 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp (T₀ ()))
  have hHm (i j : Fin n) : MemLp (H i j) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr (Lp.memLp (W j i))
  refine ⟨s, hs, hsU, T, H, hTm, hHm, ?_, ?_, ?_⟩
  · intro i φ hφ hφc hφs
    have hpair {ψ : Spacetime n → ℝ} (hψ : tsupport ψ ⊆ ball z s)
        (a : Spacetime n → ℝ) :
        (∫ y in ball z s, ψ y * a y) = ∫ y in U, ψ y * a y := by
      calc
        _ = ∫ y, ψ y * a y := setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by rw [image_eq_zero_of_notMem_tsupport (fun h => hy (hψ h)), zero_mul])
        _ = _ := (setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => by
            rw [image_eq_zero_of_notMem_tsupport
              (fun h => hy (hsU (ball_subset_closedBall (hψ h)))), zero_mul])).symm
    rw [hpair hφs, hpair (ψ := spatialDeriv i φ)
      ((tsupport_fderiv_apply_subset ℝ (spatialDirection i)).trans hφs)]
    exact hweak i φ hφ hφc (hφs.trans (ball_subset_closedBall.trans hsU))
  · intro φ hφ hφc hφs
    calc
      (∫ y in ball z s, φ y * T y) = ∫ y in ball z s, φ y * T₀ () y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        rw [show T y = T₀ () y from indicator_of_mem hy _]
      _ = _ := by simpa only [smul_eq_mul, timeDeriv] using hTweak () φ hφ hφc hφs
  · intro i j φ hφ hφc hφs
    calc
      (∫ y in ball z s, φ y * H i j y) = ∫ y in ball z s, φ y * W j i y := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
        rw [show H i j y = W j i y from indicator_of_mem hy _]
      _ = _ := by simpa only [smul_eq_mul] using hWd j i φ hφ hφc hφs

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
