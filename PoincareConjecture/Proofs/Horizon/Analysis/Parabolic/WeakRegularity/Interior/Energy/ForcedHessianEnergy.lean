import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.SecondEnergy
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.WeakPrincipalResidual
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Jets.MollifiedGradientL2
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.L2FluxEnergy

open Set Filter MeasureTheory Metric
open Poincare.Analysis.Convolution
open scoped ContDiff Topology

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Canonical

theorem exists_uniform_forced_mollified_second_energy
    {n : ℕ} {U : Set (Spacetime n)} (hU : IsOpen U)
    {C : Coefficients n} (hC : C.IsSmoothOn Set.univ)
    (hprincipalc : ∀ i j, HasCompactSupport (C.principal i j))
    (hdriftc : ∀ i, HasCompactSupport (C.drift i))
    (hzerothc : HasCompactSupport C.zeroth)
    {u f : Spacetime n → ℝ} (hu : MemLp u 2 volume) (hf : MemLp f 2 volume)
    {g : Fin n → Spacetime n → ℝ} (hg : ∀ i, MemLp (g i) 2 volume)
    (hforce : ∀ phi : Spacetime n → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ U → (∫ y, u y * C.adjoint phi y) = ∫ y, phi y * f y)
    (hweak : ∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi →
      HasCompactSupport phi → tsupport phi ⊆ U →
      (∫ y in U, phi y * g i y) = -(∫ y in U, spatialDeriv i phi y * u y))
    {z : Spacetime n} (hz : z ∈ U) {κ : ℝ} (hκ : 0 < κ)
    (hEll : ∀ ξ : Euclid n, κ * ‖ξ‖ ^ 2 ≤
      ∑ i, ∑ j, C.principal i j z * ξ i * ξ j)
    {ρ : Spacetime n → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ) :
    ∃ s : ℝ, 0 < s ∧ closedBall z s ⊆ U ∧
      ∃ ε B : ℝ, 0 < ε ∧ 0 < B ∧ ∀ r : ℝ, 0 < r → r ≤ ε →
        (∫ y in ball z s, (timeDeriv (mollifiedValue u ρ r) y) ^ 2) +
          (∫ y in ball z s, ∑ i, ∑ j,
            (spatialSecond i j (mollifiedValue u ρ r) y) ^ 2) ≤ B := by
  have hprincipal (i j : Fin n) : ContDiff ℝ ∞ (C.principal i j) :=
    contDiffOn_univ.mp (hC.1 i j)
  have hdrift (i : Fin n) : ContDiff ℝ ∞ (C.drift i) :=
    contDiffOn_univ.mp (hC.2.1 i)
  have hzeroth : ContDiff ℝ ∞ C.zeroth := contDiffOn_univ.mp hC.2.2
  have hCU : C.IsSmoothOn U :=
    ⟨fun i j => (hprincipal i j).contDiffOn, fun i => (hdrift i).contDiffOn,
      hzeroth.contDiffOn⟩
  have hul := (hu.locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hfl := (hf.locallyIntegrable (by norm_num)).locallyIntegrableOn U
  have hgl (i : Fin n) := ((hg i).locallyIntegrable (by norm_num)).locallyIntegrableOn U
  obtain ⟨δ, hδ, hδU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let V := ball z (δ / 2)
  let K₀ := closedBall z (δ / 2)
  have hK₀U : K₀ ⊆ U := by
    intro y hy
    exact hδU ((mem_closedBall.mp hy).trans_lt (by linarith))
  have hzV : z ∈ V := mem_ball_self (by positivity)
  obtain ⟨s, hs, hKV, B₀, hB₀, hsecond⟩ :=
    exists_local_second_parabolic_energy (show IsOpen V from isOpen_ball)
      (fun i j => (hprincipal i j).contDiffOn) hzV hκ hEll
  let K := closedBall z (2 * s)
  have hK : IsCompact K := isCompact_closedBall _ _
  have hKU : K ⊆ U := hKV.trans (ball_subset_closedBall.trans hK₀U)
  obtain ⟨ε₀, hε₀, hsupport⟩ := exists_uniform_translated_rescaledKernel_support_subset
    (show IsCompact K₀ from isCompact_closedBall _ _) hU hK₀U hρc
  obtain ⟨ε₁, G, hε₁, hG, hgradient⟩ :=
    exists_uniform_mollified_gradient_l2_bound hU hK hKU hul hg hweak hρ hρc
  let Q (r : ℝ) (i j : Fin n) (y : Spacetime n) :=
    C.principal i j y * lebesgueConvolution (spatialDeriv i (rescaledKernel ρ r)) (g j) y -
      lebesgueConvolution (spatialDeriv i (rescaledKernel ρ r))
        (fun x => C.principal i j x * g j x) y +
      lebesgueConvolution (rescaledKernel ρ r)
        (fun x => spatialDeriv i (C.principal i j) x * g j x) y
  have hcomm (i j : Fin n) : ∃ M : ℝ, 0 < M ∧ ∀ r : ℝ, 0 < r →
      MemLp (Q r i j) 2 volume ∧ (∫ y, Q r i j y ^ 2) ≤ M := by
    exact exists_uniform_l2_flux_commutator_bound (hprincipal i j) (hprincipalc i j)
      (hg j) hρ hρc (spatialDirection i)
  choose M hM hcomm using hcomm
  let d (i : Fin n) (y : Spacetime n) := C.drift i y * g i y
  let c (y : Spacetime n) := C.zeroth y * u y
  have hd (i : Fin n) : MemLp (d i) 2 volume :=
    (hg i).mul' ((hdrift i).continuous.memLp_top_of_hasCompactSupport (hdriftc i) volume)
  have hc : MemLp c 2 volume :=
    hu.mul' (hzeroth.continuous.memLp_top_of_hasCompactSupport hzerothc volume)
  let E (v : Spacetime n → ℝ) : ℝ := (∫ y, ‖ρ y‖) ^ 2 * ∫ y, v y ^ 2
  have hE (v : Spacetime n → ℝ) : 0 ≤ E v :=
    mul_nonneg (sq_nonneg _) (integral_nonneg (fun y => sq_nonneg _))
  let R : ℝ := 4 * ((n : ℝ) ^ 2 * (∑ i, ∑ j, M i j) +
    (n : ℝ) * (∑ i, E (d i)) + E c + E f)
  have hR : 0 ≤ R := by
    have hMsum : 0 ≤ ∑ i, ∑ j, M i j :=
      Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => (hM i j).le))
    have hEsum : 0 ≤ ∑ i, E (d i) := Finset.sum_nonneg (fun i _ => hE (d i))
    have hec := hE c
    have hef := hE f
    dsimp only [R]
    positivity
  let A : ℝ := B₀ * (R + E u + G)
  have hA : 0 < A := mul_pos hB₀ (by have := hE u; linarith)
  have hκ₂ : 0 < κ ^ 2 / 2 := by positivity
  refine ⟨s, hs, (closedBall_subset_closedBall (by linarith : s ≤ 2*s)).trans hKU,
    min ε₀ ε₁, A + A / (κ ^ 2 / 2), lt_min hε₀ hε₁, by positivity, ?_⟩
  intro r hr hrε
  have hr₀ := hrε.trans (min_le_left _ _)
  have hr₁ := hrε.trans (min_le_right _ _)
  have hη : ContDiff ℝ ∞ (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hηc : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  let w := mollifiedValue u ρ r
  have hw : ContDiff ℝ ∞ w :=
    contDiff_lebesgueConvolution (hu.locallyIntegrable (by norm_num)) hη hηc
  have hmol {v : Spacetime n → ℝ} (hv : MemLp v 2 volume) :
      MemLp (mollifiedValue v ρ r) 2 volume :=
    memLp_lebesgueConvolution hv hη.continuous hηc
  let P (y : Spacetime n) := timeDeriv w y -
    ∑ i, ∑ j, C.principal i j y * spatialSecond i j w y
  have hP (y : Spacetime n) (hy : y ∈ K) :
      P y = -(∑ i, ∑ j, Q r i j y) - (∑ i, mollifiedValue (d i) ρ r y) -
        mollifiedValue c ρ r y + mollifiedValue f ρ r y := by
    exact mollified_principal_residual_of_forcing hU (show IsOpen V from isOpen_ball)
      hCU hul hfl hforce hgl hweak hη hηc
      (fun y hy => hsupport r hr hr₀ y (ball_subset_closedBall hy)) (hKV hy)
  have hQsq (i j : Fin n) : Integrable (fun y => Q r i j y ^ 2) volume :=
    (hcomm i j r hr).1.integrable_sq
  have hdsq (i : Fin n) : Integrable (fun y => mollifiedValue (d i) ρ r y ^ 2) volume :=
    (hmol (hd i)).integrable_sq
  have hcsq := (hmol hc).integrable_sq
  have hfsq := (hmol hf).integrable_sq
  let J (y : Spacetime n) := (n : ℝ) ^ 2 * (∑ i, ∑ j, Q r i j y ^ 2) +
    (n : ℝ) * (∑ i, mollifiedValue (d i) ρ r y ^ 2) +
    mollifiedValue c ρ r y ^ 2 + mollifiedValue f ρ r y ^ 2
  have hQi := integrable_finsetSum Finset.univ
    (fun i _ => integrable_finsetSum Finset.univ (fun j _ => hQsq i j))
  have hdi := integrable_finsetSum Finset.univ (fun i _ => hdsq i)
  have hAB : Integrable (fun y => (n : ℝ) ^ 2 * (∑ i, ∑ j, Q r i j y ^ 2) +
      (n : ℝ) * (∑ i, mollifiedValue (d i) ρ r y ^ 2)) volume :=
    (hQi.const_mul ((n : ℝ) ^ 2)).add (hdi.const_mul (n : ℝ))
  have hABC : Integrable (fun y => (n : ℝ) ^ 2 * (∑ i, ∑ j, Q r i j y ^ 2) +
      (n : ℝ) * (∑ i, mollifiedValue (d i) ρ r y ^ 2) + mollifiedValue c ρ r y ^ 2) volume :=
    hAB.add hcsq
  have hJi : Integrable J volume := hABC.add hfsq
  have hJ0 (y : Spacetime n) : 0 ≤ J y := by dsimp only [J]; positivity
  have hsum (v : Fin n → ℝ) : (∑ i, v i) ^ 2 ≤ (n : ℝ) * ∑ i, v i ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin n => (1 : ℝ)) v
  have hpoint (y : Spacetime n) (hy : y ∈ K) : P y ^ 2 ≤ 4 * J y := by
    have hdouble : (∑ i, ∑ j, Q r i j y) ^ 2 ≤
        (n : ℝ) ^ 2 * (∑ i, ∑ j, Q r i j y ^ 2) := by
      calc
        _ ≤ (n : ℝ) * ∑ i, (∑ j, Q r i j y) ^ 2 := hsum _
        _ ≤ (n : ℝ) * ∑ i, (n : ℝ) * ∑ j, Q r i j y ^ 2 :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hsum _)) (Nat.cast_nonneg _)
        _ = _ := by simp only [← Finset.mul_sum, pow_two, mul_assoc]
    have hsingle := hsum (fun i => mollifiedValue (d i) ρ r y)
    rw [hP y hy]
    dsimp only [J]
    nlinarith [sq_nonneg ((∑ i, ∑ j, Q r i j y) - ∑ i, mollifiedValue (d i) ρ r y),
      sq_nonneg ((∑ i, ∑ j, Q r i j y) - mollifiedValue c ρ r y),
      sq_nonneg ((∑ i, ∑ j, Q r i j y) + mollifiedValue f ρ r y),
      sq_nonneg ((∑ i, mollifiedValue (d i) ρ r y) - mollifiedValue c ρ r y),
      sq_nonneg ((∑ i, mollifiedValue (d i) ρ r y) + mollifiedValue f ρ r y),
      sq_nonneg (mollifiedValue c ρ r y + mollifiedValue f ρ r y)]
  have hPi : IntegrableOn (fun y => P y ^ 2) K := by
    apply ContinuousOn.integrableOn_compact hK
    apply Continuous.continuousOn
    exact (((contDiff_timeDeriv hw).continuous).sub
      (continuous_finsetSum _ (fun i _ => continuous_finsetSum _ (fun j _ =>
        (hprincipal i j).continuous.mul (contDiff_spatialSecond hw i j).continuous)))).pow 2
  have hJE : (∫ y, J y) ≤ R / 4 := by
    dsimp only [J]
    rw [integral_add hABC hfsq, integral_add hAB hcsq]
    rw [integral_add (hQi.const_mul _) (hdi.const_mul _), integral_const_mul, integral_const_mul]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hQsq i j)),
      integral_finsetSum _ (fun i _ => hdsq i)]
    simp_rw [integral_finsetSum _ (fun j _ => hQsq _ j)]
    have hQb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => (hcomm i j r hr).2))
    have hdb := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
      integral_mollifiedValue_sq_le (hd i) hρ.continuous hρc hr)
    have hcb := integral_mollifiedValue_sq_le hc hρ.continuous hρc hr
    have hfb := integral_mollifiedValue_sq_le hf hρ.continuous hρc hr
    have hQb' := mul_le_mul_of_nonneg_left hQb (sq_nonneg (n : ℝ))
    have hdb' := mul_le_mul_of_nonneg_left hdb (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
    dsimp only [R, E]
    linarith
  have hPres : (∫ y in K, P y ^ 2) ≤ R := by
    have hi := integral_mono_ae hPi (hJi.const_mul 4).integrableOn
      (by filter_upwards [ae_restrict_mem hK.measurableSet] with y hy; exact hpoint y hy)
    rw [integral_const_mul] at hi
    have hk := setIntegral_le_integral hJi (Eventually.of_forall hJ0) (s := K)
    linarith
  have huK : (∫ y in K, w y ^ 2) ≤ E u :=
    (setIntegral_le_integral (hmol hu).integrable_sq
      (Eventually.of_forall (fun y => sq_nonneg _))).trans
        (integral_mollifiedValue_sq_le hu hρ.continuous hρc hr)
  have hgK : (∫ y in K, ∑ i, spatialDeriv i w y ^ 2) ≤ G := hgradient r hr hr₁
  have hwi : IntegrableOn (fun y => w y ^ 2) K := (hmol hu).integrable_sq.integrableOn
  have hgi : IntegrableOn (fun y => ∑ i, spatialDeriv i w y ^ 2) K :=
    (continuous_finsetSum _ (fun i _ => (contDiff_spatialDeriv hw i).continuous.pow 2)).continuousOn
      |>.integrableOn_compact hK
  have hweighted := hsecond w hw
  change _ ≤ B₀ * (∫ y in K, P y ^ 2 + w y ^ 2 + ∑ i, spatialDeriv i w y ^ 2) at hweighted
  have hPwi : IntegrableOn (fun y => P y ^ 2 + w y ^ 2) K := hPi.add hwi
  rw [integral_add hPwi hgi, integral_add hPi hwi] at hweighted
  have hright := mul_le_mul_of_nonneg_left (add_le_add (add_le_add hPres huK) hgK) hB₀.le
  have htotal : (∫ y in ball z s, timeDeriv w y ^ 2) + (κ ^ 2 / 2) *
      (∫ y in ball z s, ∑ i, ∑ j, spatialSecond i j w y ^ 2) ≤ A := hweighted.trans hright
  have ht0 : 0 ≤ ∫ y in ball z s, timeDeriv w y ^ 2 := integral_nonneg (fun y => sq_nonneg _)
  have hh0 : 0 ≤ ∫ y in ball z s, ∑ i, ∑ j, spatialSecond i j w y ^ 2 :=
    integral_nonneg (fun y => Finset.sum_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg _)))
  have ht : (∫ y in ball z s, timeDeriv w y ^ 2) ≤ A := by nlinarith
  have hh : (∫ y in ball z s, ∑ i, ∑ j, spatialSecond i j w y ^ 2) ≤ A / (κ ^ 2 / 2) := by
    apply (le_div_iff₀ hκ₂).mpr
    nlinarith
  exact add_le_add ht hh

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
