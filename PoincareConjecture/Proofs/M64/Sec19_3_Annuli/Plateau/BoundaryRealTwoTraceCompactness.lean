import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryRealTraceOffset
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseRadialFlip













set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S
local notation "nu" => volume.restrict (Icc (0 : ℝ) curvePeriod)
local notation "e0" => EuclideanSpace.single (0 : Fin 2) (1 : ℝ)
local notation "e1" => EuclideanSpace.single (1 : Fin 2) (1 : ℝ)




theorem m64WeakPhase_monotone_two_real_traces_subsequence
    (u : ℕ → LoopPlane → ℝ) (V : ℕ → Fin 2 → LoopPlane → ℝ)
    (b0 b1 : ℕ → ℝ → ℝ)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hw : ∀ j i, HasWeakPartialDeriv i (V j i) (u j) S)
    (hm0 : ∀ j, Monotone (b0 j)) (hm1 : ∀ j, Monotone (b1 j)) {D B C : ℝ}
    (hp0 : ∀ j x, b0 j (x + curvePeriod) = b0 j x + D)
    (hp1 : ∀ j x, b1 j (x + curvePeriod) = b1 j x + D)
    (hB : ∀ j, |b0 j 0| ≤ B)
    (hC : ∀ j i, (∫ p in S, (V j i p) ^ 2) ≤ C)
    (hseam : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V j 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u j p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) * b1 j x - phi (annulusPoint x 0) * b0 j x) :
    ∃ (k : ℕ → ℕ) (U : Lp ℝ 2 mu) (W : Fin 2 → Lp ℝ 2 mu) (L0 L1 : ℝ → ℝ),
      StrictMono k ∧ WeakConverges (fun j => (hu (k j)).toLp (u (k j))) U ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p))) ∧
      (∀ i, HasWeakPartialDeriv i (W i) U S) ∧
      Monotone L0 ∧ Continuous L0 ∧ Monotone L1 ∧ Continuous L1 ∧
      (∀ x, L0 (x + curvePeriod) = L0 x + D) ∧
      (∀ x, L1 (x + curvePeriod) = L1 x + D) ∧ |L0 0| ≤ B ∧
      (∀ x, Tendsto (fun j => b0 (k j) x) atTop (𝓝 (L0 x))) ∧
      (∀ x, Tendsto (fun j => b1 (k j) x) atTop (𝓝 (L1 x))) ∧
      (∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
        (∫ p in S, phi p * W 0 p) + (∫ p in S, fderiv ℝ phi p e0 * U p) =
          D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) ∧
      ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * U p) =
          ∫ x in Icc (0 : ℝ) curvePeriod,
            phi (annulusPoint x 1) * L1 x - phi (annulusPoint x 0) * L0 x := by
  let B1 := B + |D| + (volume.real S + C) / (2 * curvePeriod)
  have hB1 (j : ℕ) : |b1 j 0| ≤ B1 := m64WeakPhase_upper_zero_bound
    (u j) (V j 1) (b0 j) (b1 j) (hV j 1) (hm0 j) (hm1 j)
    (hp0 j) (hp1 j) (hB j) (hC j 1) (hgreen j)
  have hbounded := m64MonotoneAffinePhase_locally_bounded b1 hm1 hp1 hB1
  obtain ⟨k0, L1, hk0, hL1, hliminf, hcontlim, haeL1⟩ :=
    M64.monotone_sequence_subsequence_ae b1 hm1 hbounded
  have hperiod1 (x : ℝ) : L1 (x + curvePeriod) = L1 x + D := by
    obtain ⟨lo, hi, hbound⟩ := hbounded x
    have hbelow : IsBoundedUnder (· ≥ ·) atTop (fun j => b1 (k0 j) x) :=
      isBoundedUnder_of ⟨lo, fun j => (hbound (k0 j)).1⟩
    have habove : IsBoundedUnder (· ≤ ·) atTop (fun j => b1 (k0 j) x) :=
      isBoundedUnder_of ⟨hi, fun j => (hbound (k0 j)).2⟩
    rw [hliminf, hliminf]
    simp_rw [hp1]
    exact liminf_add_const atTop (fun j => b1 (k0 j) x) D habove.isCobounded_ge hbelow
  have hlower (j : ℕ) (phi : LoopPlane → ℝ) (hp : ContDiff ℝ 1 phi)
      (htop : ∀ x : ℝ, phi (annulusPoint x 1) = 0) :
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b0 j x) := by
    simpa only [htop, zero_mul, zero_sub, integral_neg] using hgreen j phi hp
  obtain ⟨k1, U, W, L0, hk1, hU, hW, ha, hweak, hL0, hc0, hperiod0, hzero,
      hlim0, hs, -⟩ := m64WeakPhase_monotone_real_trace_subsequence
    (fun j => u (k0 j)) (fun j => V (k0 j)) (fun j => b0 (k0 j))
    (fun j => hu (k0 j)) (fun j => hV (k0 j)) (fun j => hw (k0 j))
    (fun j => hm0 (k0 j)) (fun j => hp0 (k0 j)) (fun j => hB (k0 j))
    (fun j => hC (k0 j)) (fun j => hseam (k0 j)) (fun j => hlower (k0 j))
  let k := k0 ∘ k1
  have hbnd0 (j : ℕ) : ∀ᵐ x ∂nu, ‖b0 j x‖ ≤ B + |D| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact m64MonotoneAffinePhase_bound_on_period (b0 j) (hm0 j) (hp0 j) (hB j) hx
  have hbnd1 (j : ℕ) : ∀ᵐ x ∂nu, ‖b1 j x‖ ≤ B1 + |D| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact m64MonotoneAffinePhase_bound_on_period (b1 j) (hm1 j) (hp1 j) (hB1 j) hx
  have hgreenL (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi) :
      (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * U p) =
        ∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) * L1 x - phi (annulusPoint x 0) * L0 x := by
    have hph (s : ℝ) : Continuous (fun x => phi (annulusPoint x s)) :=
      hphi.continuous.comp (by unfold annulusPoint; fun_prop)
    have ht : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 1) * b1 (k j) x - phi (annulusPoint x 0) * b0 (k j) x)
        atTop (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod,
          phi (annulusPoint x 1) * L1 x - phi (annulusPoint x 0) * L0 x)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => ‖phi (annulusPoint x 1)‖ * (B1 + |D|) +
          ‖phi (annulusPoint x 0)‖ * (B + |D|))
      · intro j
        exact ((hph 1).aestronglyMeasurable.mul (hm1 (k j)).measurable.aestronglyMeasurable).sub
          ((hph 0).aestronglyMeasurable.mul (hm0 (k j)).measurable.aestronglyMeasurable)
      · exact (((hph 1).norm.mul continuous_const).add
          ((hph 0).norm.mul continuous_const)).integrableOn_Icc
      · intro j
        filter_upwards [hbnd1 (k j), hbnd0 (k j)] with x hx1 hx0
        apply (norm_sub_le _ _).trans
        simp only [norm_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left hx1 (norm_nonneg _))
          (mul_le_mul_of_nonneg_left hx0 (norm_nonneg _))
      · filter_upwards [ae_restrict_of_ae haeL1] with x hx
        exact (tendsto_const_nhds.mul (hx.comp hk1.tendsto_atTop)).sub
          (tendsto_const_nhds.mul (hlim0 x))
    let dphi := fun p : LoopPlane => fderiv ℝ phi p e1
    have hp : MemLp phi 2 mu := by
      apply (memLp_two_iff_integrable_sq hphi.continuous.aestronglyMeasurable).mpr
      exact (hphi.continuous.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset
    have hdc : Continuous dphi := (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
    have hdp : MemLp dphi 2 mu := by
      apply (memLp_two_iff_integrable_sq hdc.aestronglyMeasurable).mpr
      exact (hdc.pow 2).continuousOn.integrableOn_compact
        m64AnnulusDomain_isCompact |>.mono_set interior_subset
    simpa only [testIntegral_apply, smul_eq_mul, dphi] using
      M64.weak_affine_identity_of_tendsto hU (hW 1) (testIntegral (F := ℝ) phi hp)
        (testIntegral dphi hdp) ht (fun j => by
          simpa only [testIntegral_toLp, smul_eq_mul, dphi, k, Function.comp_def]
            using hgreen (k j) phi hphi)
  have hc1 : Continuous L1 := by
    apply m64WeakPhase_monotone_affine_upper_trace_continuous U (fun i => W i) L1 D
      (fun i => Lp.memLp (W i)) hL1 hperiod1 hs
    intro phi hphi hbottom
    simpa only [hbottom, zero_mul, sub_zero] using hgreenL phi hphi
  have hlim1 (x : ℝ) : Tendsto (fun j => b1 (k j) x) atTop (𝓝 (L1 x)) :=
    (hcontlim x hc1.continuousAt).comp hk1.tendsto_atTop
  exact ⟨k, U, W, L0, L1, hk0.comp hk1, hU, hW, ha, hweak, hL0, hc0, hL1, hc1,
    hperiod0, hperiod1, hzero, hlim0, hlim1, hs, hgreenL⟩

end PoincareConjecture
