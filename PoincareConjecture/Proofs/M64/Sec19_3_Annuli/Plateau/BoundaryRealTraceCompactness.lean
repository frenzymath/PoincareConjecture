import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeakPhaseExtraction
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryMonotonePhaseBounds
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.MonotoneHelly
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.FreeBoundaryCompactness.VaryingGreen












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

private theorem scalar_green_limit
    (u v : ℕ → LoopPlane → ℝ) (hu : ∀ j, MemLp (u j) 2 mu)
    (hv : ∀ j, MemLp (v j) 2 mu) {U V : Lp ℝ 2 mu}
    (hU : WeakConverges (fun j => (hu j).toLp (u j)) U)
    (hV : WeakConverges (fun j => (hv j).toLp (v j)) V)
    (i : Fin 2) (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi)
    {c : ℕ → ℝ} {c0 : ℝ} (hc : Tendsto c atTop (𝓝 c0))
    (hseq : ∀ j, (∫ p in S, phi p * v j p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * u j p) = c j) :
    (∫ p in S, phi p * V p) +
      (∫ p in S, fderiv ℝ phi p (EuclideanSpace.single i 1) * U p) = c0 := by
  let dphi := fun p : LoopPlane => fderiv ℝ phi p (EuclideanSpace.single i 1)
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
    M64.weak_affine_identity_of_tendsto hU hV (testIntegral (F := ℝ) phi hp)
      (testIntegral dphi hdp) hc (fun j => by
        simpa only [testIntegral_toLp, smul_eq_mul, dphi] using hseq j)






theorem m64WeakPhase_monotone_real_trace_subsequence
    (u : ℕ → LoopPlane → ℝ) (V : ℕ → Fin 2 → LoopPlane → ℝ) (b : ℕ → ℝ → ℝ)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hw : ∀ j i, HasWeakPartialDeriv i (V j i) (u j) S)
    (hb : ∀ j, Monotone (b j)) {D B C : ℝ}
    (hp : ∀ j x, b j (x + curvePeriod) = b j x + D) (hB : ∀ j, |b j 0| ≤ B)
    (hC : ∀ j i, (∫ p in S, (V j i p) ^ 2) ≤ C)
    (hseam : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
      (∫ p in S, phi p * V j 0 p) + (∫ p in S, fderiv ℝ phi p e0 * u j p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s))
    (hgreen : ∀ j, ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
      (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
      (∫ p in S, phi p * V j 1 p) + (∫ p in S, fderiv ℝ phi p e1 * u j p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * b j x)) :
    ∃ (k : ℕ → ℕ) (U : Lp ℝ 2 mu) (W : Fin 2 → Lp ℝ 2 mu) (L : ℝ → ℝ),
      StrictMono k ∧ WeakConverges (fun j => (hu (k j)).toLp (u (k j))) U ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p))) ∧
      (∀ i, HasWeakPartialDeriv i (W i) U S) ∧
      Monotone L ∧ Continuous L ∧ (∀ x, L (x + curvePeriod) = L x + D) ∧ |L 0| ≤ B ∧
      (∀ x, Tendsto (fun j => b (k j) x) atTop (𝓝 (L x))) ∧
      (∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ s ∈ Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) →
        (∫ p in S, phi p * W 0 p) + (∫ p in S, fderiv ℝ phi p e0 * U p) =
          D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s)) ∧
      ∀ phi : LoopPlane → ℝ, ContDiff ℝ 1 phi →
        (∀ x : ℝ, phi (annulusPoint x 1) = 0) →
        (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * U p) =
          -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * L x) := by
  have hbounded := m64MonotoneAffinePhase_locally_bounded b hb hp hB
  obtain ⟨k0, L, hk0, hL, hliminf, hcontlim, haeL⟩ :=
    M64.monotone_sequence_subsequence_ae b hb hbounded
  have hperiod (x : ℝ) : L (x + curvePeriod) = L x + D := by
    obtain ⟨lo, hi, hbound⟩ := hbounded x
    have hbelow : IsBoundedUnder (· ≥ ·) atTop (fun j => b (k0 j) x) :=
      isBoundedUnder_of ⟨lo, fun j => (hbound (k0 j)).1⟩
    have habove : IsBoundedUnder (· ≤ ·) atTop (fun j => b (k0 j) x) :=
      isBoundedUnder_of ⟨hi, fun j => (hbound (k0 j)).2⟩
    rw [hliminf, hliminf]
    simp_rw [hp]
    exact liminf_add_const atTop (fun j => b (k0 j) x) D habove.isCobounded_ge hbelow
  have htraceBound (j : ℕ) : ∀ᵐ x ∂nu, ‖b j x‖ ≤ B + |D| := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    exact m64MonotoneAffinePhase_bound_on_period (b j) (hb j) (hp j) (hB j) hx
  have hbLp (j : ℕ) : MemLp (b j) 2 nu :=
    MemLp.of_bound (hb j).measurable.aestronglyMeasurable (B + |D|) (htraceBound j)
  have htraceEnergy (j : ℕ) : (∫ x in Icc (0 : ℝ) curvePeriod, (b j x) ^ 2) ≤
      curvePeriod * (B + |D|) ^ 2 := by
    have hB0 : 0 ≤ B + |D| := add_nonneg ((abs_nonneg _).trans (hB 0)) (abs_nonneg _)
    have h := integral_mono_ae (hbLp j).integrable_sq
      (integrableOn_const (μ := volume) (C := (B + |D|) ^ 2) isCompact_Icc.measure_ne_top)
      ((htraceBound j).mono fun x hx => by
        simpa only [Real.norm_eq_abs, sq_abs] using
          (sq_le_sq₀ (norm_nonneg _) hB0).mpr hx)
    simpa only [setIntegral_const, Real.volume_real_Icc, sub_zero,
      max_eq_left (by unfold curvePeriod; positivity : 0 ≤ curvePeriod), smul_eq_mul] using h
  have hbulk (j : ℕ) : (∫ p in S, (u j p) ^ 2) ≤
      2 * (C + curvePeriod * (B + |D|) ^ 2) := by
    have h := m64WeakPhase_lower_trace_l2_bound (u j) (V j 1) (b j)
      (hu j) (hV j 1) (hbLp j) (hgreen j)
    linarith [hC j 1, htraceEnergy j]
  obtain ⟨k1, U, W, hk1, hU, hW, ha, hweak⟩ := m64WeakPhase_weak_ae_subsequence
    (fun j => u (k0 j)) (fun j => V (k0 j)) (fun j => hu (k0 j))
    (fun j => hV (k0 j)) (fun j => hw (k0 j)) (fun j => hbulk (k0 j)) (fun j => hC (k0 j))
  let k := k0 ∘ k1
  have hseamL (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi)
      (hmatch : ∀ s ∈ Icc (0 : ℝ) 1,
        phi (annulusPoint curvePeriod s) = phi (annulusPoint 0 s)) :
      (∫ p in S, phi p * W 0 p) + (∫ p in S, fderiv ℝ phi p e0 * U p) =
        D * ∫ s in Icc (0 : ℝ) 1, phi (annulusPoint curvePeriod s) :=
    scalar_green_limit (fun j => u (k j)) (fun j => V (k j) 0) (fun j => hu (k j))
      (fun j => hV (k j) 0) hU (hW 0) 0 phi hphi tendsto_const_nhds
      (fun j => hseam (k j) phi hphi hmatch)
  have hgreenL (phi : LoopPlane → ℝ) (hphi : ContDiff ℝ 1 phi)
      (htop : ∀ x : ℝ, phi (annulusPoint x 1) = 0) :
      (∫ p in S, phi p * W 1 p) + (∫ p in S, fderiv ℝ phi p e1 * U p) =
        -(∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * L x) := by
    have hph : Continuous (fun x => phi (annulusPoint x 0)) :=
      hphi.continuous.comp (by unfold annulusPoint; fun_prop)
    have ht : Tendsto (fun j => ∫ x in Icc (0 : ℝ) curvePeriod,
        phi (annulusPoint x 0) * b (k j) x) atTop
        (𝓝 (∫ x in Icc (0 : ℝ) curvePeriod, phi (annulusPoint x 0) * L x)) := by
      apply tendsto_integral_of_dominated_convergence
        (fun x => ‖phi (annulusPoint x 0)‖ * (B + |D|))
      · intro j
        exact hph.aestronglyMeasurable.mul (hb (k j)).measurable.aestronglyMeasurable
      · exact (hph.norm.mul continuous_const).integrableOn_Icc
      · intro j
        filter_upwards [htraceBound (k j)] with x hx
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left hx (norm_nonneg _)
      · filter_upwards [ae_restrict_of_ae haeL] with x hx
        exact tendsto_const_nhds.mul (hx.comp hk1.tendsto_atTop)
    exact scalar_green_limit (fun j => u (k j)) (fun j => V (k j) 1) (fun j => hu (k j))
      (fun j => hV (k j) 1) hU (hW 1) 1 phi hphi ht.neg
      (fun j => hgreen (k j) phi hphi htop)
  have hcontinuous : Continuous L := m64WeakPhase_monotone_affine_trace_continuous U
    (fun i => W i) L D (fun i => Lp.memLp (W i)) hL hperiod hseamL hgreenL
  have hlim (x : ℝ) : Tendsto (fun j => b (k j) x) atTop (𝓝 (L x)) :=
    (hcontlim x hcontinuous.continuousAt).comp hk1.tendsto_atTop
  have hL0 : |L 0| ≤ B := le_of_tendsto' (hlim 0).abs (fun j => hB (k j))
  exact ⟨k, U, W, L, hk0.comp hk1, hU, hW, ha, hweak, hL, hcontinuous,
    hperiod, hL0, hlim, hseamL, hgreenL⟩

end PoincareConjecture
