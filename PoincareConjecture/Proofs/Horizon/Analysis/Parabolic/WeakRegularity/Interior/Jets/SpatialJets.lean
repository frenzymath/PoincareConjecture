




import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.InitialEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.RescaledApproximation
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.WeakDerivativeLimit









open Set Filter MeasureTheory Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology ENNReal

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Parabolic.WeakRegularity.Canonical

variable {n : ℕ}

local instance : (volume : Measure (Spacetime n)).IsAddHaarMeasure := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance


theorem exists_local_spatial_weak_derivatives
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn U)
    (hEll : C.IsUniformlyEllipticOn U)
    {u : Spacetime n → ℝ} (hu : ContinuousOn u U)
    (hw : WeakSolutionOn C u U) {z : Spacetime n} (hz : z ∈ U) :
    ∃ r : ℝ, 0 < r ∧ closedBall z r ⊆ U ∧
      MemLp u 2 (volume.restrict (ball z r)) ∧
      ∃ V : Fin n → Lp ℝ 2 (volume.restrict (ball z r)),
        ∀ i (φ : Spacetime n → ℝ), ContDiff ℝ ∞ φ → HasCompactSupport φ →
          tsupport φ ⊆ ball z r →
          (∫ y in ball z r, φ y * V i y) =
            -(∫ y in ball z r, spatialDeriv i φ y * u y) := by
  obtain ⟨W, C', u', hW, hzW, hWU, hC', hpc, hbc, hcc, hu', huc,
    hpEq, hbEq, hcEq, huEq, hw'⟩ := exists_weak_compact_extension hU hC hu hw hz
  have hC'W : C'.IsSmoothOn W :=
    ⟨fun i j => (hC'.1 i j).mono (subset_univ W),
      fun i => (hC'.2.1 i).mono (subset_univ W), hC'.2.2.mono (subset_univ W)⟩
  have hEll' : C'.IsUniformlyEllipticOn W := by
    obtain ⟨κ, hκ, hEllκ⟩ := hEll
    refine ⟨κ, hκ, ?_⟩
    intro y hy ξ
    simp_rw [hpEq _ _ hy]
    exact hEllκ y (hWU hy) ξ
  let ρb : ContDiffBump (0 : Spacetime n) :=
    { rIn := 1
      rOut := 2
      rIn_pos := by norm_num
      rIn_lt_rOut := by norm_num }
  let ρ : Spacetime n → ℝ := ρb.normed volume
  have hρ : ContDiff ℝ ∞ ρ := ρb.contDiff_normed
  have hρc : HasCompactSupport ρ := ρb.hasCompactSupport_normed
  have hmass : (∫ y, ρ y) = 1 := ρb.integral_normed
  obtain ⟨χ, hχW, ε, B, hε, hB, henergy⟩ :=
    exists_local_mollified_gradient_energy hW hC'W hEll' hu'.continuousOn hw' hzW hρ hρc
  let s : Set (Spacetime n) := ball z χ.rIn
  have hs : IsOpen s := isOpen_ball
  have hclosedW : closedBall z χ.rIn ⊆ W := by
    apply Subset.trans _ hχW
    rw [χ.tsupport_eq]
    exact closedBall_subset_closedBall χ.rIn_lt_rOut.le
  have hsW : s ⊆ W := ball_subset_closedBall.trans hclosedW
  have hχone {y : Spacetime n} (hy : y ∈ s) : χ y = 1 :=
    χ.one_of_mem_closedBall (ball_subset_closedBall hy)
  letI : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.mpr measure_ball_ne_top
  let r : ℕ → ℝ := fun m => ε / ((m : ℝ) + 1)
  have hr (m : ℕ) : 0 < r m := by dsimp only [r]; positivity
  have hrε (m : ℕ) : r m ≤ ε :=
    div_le_self hε.le (by have h := Nat.cast_nonneg (α := ℝ) m; linarith)
  have hrlim : Tendsto r atTop (𝓝 0) := by
    have ht := (tendsto_const_nhds (x := ε)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [r, div_eq_mul_inv, one_mul, mul_zero] using ht
  let f : ℕ → Spacetime n → ℝ := fun m => mollifiedValue u' ρ (r m)
  have hf (m : ℕ) : ContDiff ℝ ∞ (f m) := by
    apply contDiff_lebesgueConvolution hu'.locallyIntegrable
    · exact contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
    · exact (hρc.comp_homeomorph
        (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
  have hcutLp {g : Spacetime n → ℝ} (hg : Continuous g) :
      MemLp g 2 (volume.restrict s) := by
    have hcut : MemLp (fun y => χ y * g y) 2 (volume.restrict s) :=
      (χ.continuous.mul hg).memLp_of_hasCompactSupport χ.hasCompactSupport.mul_right
    apply MemLp.ae_eq _ hcut
    filter_upwards [ae_restrict_mem hs.measurableSet] with y hy
    simp only [hχone hy, one_mul]
  have huLp : MemLp u' 2 (volume.restrict s) := hcutLp hu'
  have hfm (m : ℕ) : MemLp (f m) 2 (volume.restrict s) := hcutLp (hf m).continuous
  have hdf (m : ℕ) (i : Fin n) : MemLp
      (fun y => fderiv ℝ (f m) y (spatialDirection i)) 2 (volume.restrict s) :=
    hcutLp (contDiff_spatialDeriv (hf m) i).continuous
  have hlim : TendstoUniformlyOn f u' atTop s :=
    (tendstoUniformly_mollifiedValue hu' huc hρ hρc hmass hr hrlim).tendstoUniformlyOn
  have hnorm (m : ℕ) (i : Fin n) :
      ‖(hdf m i).toLp (fun y => fderiv ℝ (f m) y (spatialDirection i))‖ ^ 2 =
        ∫ y in s, (spatialDeriv i (f m) y) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    simp only [real_inner_self_eq_norm_sq]
    apply integral_congr_ae
    filter_upwards [(hdf m i).coeFn_toLp] with y hy
    rw [hy]
    simp only [Real.norm_eq_abs, sq_abs, spatialDeriv]
  have hgradint (m : ℕ) (i : Fin n) : Integrable
      (fun y => (χ y * spatialDeriv i (f m) y) ^ 2) :=
    ((χ.continuous.mul (contDiff_spatialDeriv (hf m) i).continuous).pow 2).integrable_of_hasCompactSupport
      (HasCompactSupport.intro χ.hasCompactSupport (fun y hy => by
        simp [image_eq_zero_of_notMem_tsupport hy]))
  have hdfint (m : ℕ) (i : Fin n) : IntegrableOn
      (fun y => spatialDeriv i (f m) y ^ 2) s := by
    apply ((hgradint m i).integrableOn).congr
    filter_upwards [ae_restrict_mem hs.measurableSet] with y hy
    simp only [hχone hy, one_mul]
  have henergyLp (m : ℕ) :
      (∑ i, ‖(hdf m i).toLp (fun y => fderiv ℝ (f m) y (spatialDirection i))‖ ^ 2) ≤ B := by
    simp_rw [hnorm]
    rw [← integral_finsetSum _ (fun i _ => hdfint m i)]
    calc
      (∫ y in s, ∑ i, spatialDeriv i (f m) y ^ 2) =
          ∫ y in s, ∑ i, (χ y * spatialDeriv i (f m) y) ^ 2 := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem hs.measurableSet] with y hy
        simp only [hχone hy, one_mul]
      _ ≤ ∫ y, ∑ i, (χ y * spatialDeriv i (f m) y) ^ 2 :=
        setIntegral_le_integral (integrable_finsetSum _ (fun i _ => hgradint m i))
          (Eventually.of_forall (fun y => Finset.sum_nonneg (fun i _ => sq_nonneg _)))
      _ ≤ B := henergy (r m) (hr m) (hrε m)
  obtain ⟨V, k, hk, hweak, hdist, hVenergy⟩ :=
    weak_derivatives_of_uniform_limit hs huLp f (fun m => (hf m).contDiffOn.of_le (by simp))
      spatialDirection hfm hdf hlim henergyLp
  have hueq : u' =ᵐ[volume.restrict s] u := by
    filter_upwards [ae_restrict_mem hs.measurableSet] with y hy
    exact huEq (hsW hy)
  refine ⟨χ.rIn, χ.rIn_pos, hclosedW.trans hWU, MemLp.ae_eq hueq huLp, V, ?_⟩
  intro i φ hφ hφc hφs
  have hid := hdist i φ hφ hφc hφs
  simp only [smul_eq_mul] at hid
  rw [hid]
  congr 1
  exact integral_congr_ae (hueq.mono (fun y hy =>
    congrArg (fun q : ℝ => spatialDeriv i φ y * q) hy))

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
