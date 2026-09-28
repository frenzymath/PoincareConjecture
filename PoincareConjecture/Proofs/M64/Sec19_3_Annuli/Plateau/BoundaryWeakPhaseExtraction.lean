import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryWeightedPhaseCompactness
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.HilbertExtraction
import PoincareConjecture.Proofs.Horizon.Analysis.Sobolev.WeakCompactness.StrongLimit
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter MeasureTheory
open scoped ContDiff Topology ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.WeakCompactness

local notation "S" => interior m64AnnulusDomain
local notation "mu" => volume.restrict S

private theorem weighted_strong_weak_ae_subsequence
    (u : ℕ → LoopPlane → ℝ) (hu : ∀ j, MemLp (u j) 2 mu)
    (rho : LoopPlane → ℝ) (hrho : Continuous rho)
    (hpos : ∀ p ∈ S, 0 < rho p) (h01 : ∀ p, rho p ∈ Icc (0 : ℝ) 1)
    (hF : ∀ j, MemLp (fun p => rho p * u j p) 2 volume)
    {U : Lp ℝ 2 mu} {Z : Lp ℝ 2 (volume : Measure LoopPlane)}
    (hw : WeakConverges (fun j => (hu j).toLp (u j)) U)
    (hs : Tendsto (fun j => (hF j).toLp (fun p => rho p * u j p)) atTop (𝓝 Z)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧
      ∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p)) := by
  have htop : MemLp rho ⊤ mu := memLp_top_of_bound hrho.aestronglyMeasurable 1
    (ae_of_all _ (fun p => by simpa only [Real.norm_eq_abs, abs_of_nonneg (h01 p).1]
      using (h01 p).2))
  let L : Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
    (ContinuousLinearMap.lsmul ℝ ℝ).holderL mu ⊤ 2 2 (htop.toLp rho)
  have hL (v : Lp ℝ 2 mu) :
      (L v : LoopPlane → ℝ) =ᵐ[mu] fun p => rho p * v p := by
    change (ContinuousLinearMap.lsmul ℝ ℝ).holder 2 (htop.toLp rho) v =ᵐ[mu] _
    filter_upwards [(ContinuousLinearMap.lsmul ℝ ℝ).coeFn_holder (r := 2) (htop.toLp rho) v,
      htop.coeFn_toLp] with p hp hpr
    simp only [hp, hpr, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hmu : mu ≤ (1 : ℝ≥0∞) • volume := by
    simpa only [one_smul] using (Measure.restrict_le_self : mu ≤ volume)
  let R : Lp ℝ 2 (volume : Measure LoopPlane) →L[ℝ] Lp ℝ 2 mu :=
    Lp.LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu
  have hR (v : Lp ℝ 2 (volume : Measure LoopPlane)) :
      (R v : LoopPlane → ℝ) =ᵐ[mu] v :=
    Lp.coeFn_LpToLpOfMeasureLeSMul (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) hmu v
  have heq (j : ℕ) : R ((hF j).toLp (fun p => rho p * u j p)) = L ((hu j).toLp (u j)) := by
    apply Lp.ext
    filter_upwards [hR ((hF j).toLp (fun p => rho p * u j p)),
      ae_restrict_of_ae (hF j).coeFn_toLp, hL ((hu j).toLp (u j)), (hu j).coeFn_toLp]
      with p hp hpf hpl hpu
    rw [hp, hpf, hpl, hpu]
  have hstrong : Tendsto (fun j => L ((hu j).toLp (u j))) atTop (𝓝 (R Z)) :=
    ((R.continuous.tendsto Z).comp hs).congr' (Eventually.of_forall heq)
  have hweak : WeakConverges (fun j => L ((hu j).toLp (u j))) (L U) :=
    fun A => hw (A.comp L)
  have hlim : L U = R Z := eq_of_strong_and_weak_limit hstrong hweak
  have hZ : ∀ᵐ p ∂mu, Z p = rho p * U p := by
    filter_upwards [hL U, hR Z] with p hp hq
    rw [hlim] at hp
    exact hq.symm.trans hp
  obtain ⟨k, hk, ha⟩ := (tendstoInMeasure_of_tendsto_Lp hs).exists_seq_tendsto_ae
  refine ⟨k, hk, ?_⟩
  have hcoe : ∀ᵐ p ∂volume, ∀ j,
      ((hF (k j)).toLp (fun p => rho p * u (k j) p)) p = rho p * u (k j) p :=
    ae_all_iff.mpr (fun j => (hF (k j)).coeFn_toLp)
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_of_ae hcoe, hZ,
    ae_restrict_mem isOpen_interior.measurableSet] with p hp hrep hz hpS
  have hm : Tendsto (fun j => rho p * u (k j) p) atTop (𝓝 (rho p * U p)) := by
    rw [← hz]
    exact hp.congr' (Eventually.of_forall hrep)
  simpa only [mul_div_cancel_left₀ _ (hpos p hpS).ne'] using hm.div_const (rho p)

private theorem phase_norm_sq (f : LoopPlane → ℝ) (hf : MemLp f 2 mu) :
    ‖hf.toLp f‖ ^ 2 = ∫ p in S, (f p) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with p hp
  simp only [real_inner_self_eq_norm_sq, hp, Real.norm_eq_abs, sq_abs]






theorem m64WeakPhase_weak_ae_subsequence
    (u : ℕ → LoopPlane → ℝ) (V : ℕ → Fin 2 → LoopPlane → ℝ)
    (hu : ∀ j, MemLp (u j) 2 mu) (hV : ∀ j i, MemLp (V j i) 2 mu)
    (hw : ∀ j i, HasWeakPartialDeriv i (V j i) (u j) S)
    {A C : ℝ} (hA : ∀ j, (∫ p in S, (u j p) ^ 2) ≤ A)
    (hC : ∀ j i, (∫ p in S, (V j i p) ^ 2) ≤ C) :
    ∃ (k : ℕ → ℕ) (U : Lp ℝ 2 mu) (W : Fin 2 → Lp ℝ 2 mu),
      StrictMono k ∧ WeakConverges (fun j => (hu (k j)).toLp (u (k j))) U ∧
      (∀ i, WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i)) ∧
      (∀ᵐ p ∂mu, Tendsto (fun j => u (k j) p) atTop (𝓝 (U p))) ∧
      ∀ i, HasWeakPartialDeriv i (W i) U S := by
  let : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let H (j : ℕ) : MemW1pWitness 2 (u j) S :=
    { memLp := hu j
      weakGrad := fun p => WithLp.toLp 2 (fun i => V j i p)
      weakGrad_component_memLp := hV j
      isWeakGrad := hw j }
  obtain ⟨rho, hrho, hpos, h01, -, hF, hcompact⟩ :=
    m64WeakPhase_weighted_l2_isCompact u H hA hC
  obtain ⟨Z, -, k0, hk0, hZ⟩ := hcompact.isSeqCompact
    (fun j => subset_closure (mem_range_self j))
  have huNorm (j : ℕ) : ‖(hu j).toLp (u j)‖ ≤ Real.sqrt (max A 0) := by
    apply Real.le_sqrt_of_sq_le
    rw [phase_norm_sq]
    exact (hA j).trans (le_max_left _ _)
  have hVNorm (j : ℕ) (i : Fin 2) : ‖(hV j i).toLp (V j i)‖ ≤ Real.sqrt (max C 0) := by
    apply Real.le_sqrt_of_sq_le
    rw [phase_norm_sq]
    exact (hC j i).trans (le_max_left _ _)
  obtain ⟨U, k1, hk1, hU⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hu (k0 j)).toLp (u (k0 j))) (fun j => huNorm (k0 j))
  obtain ⟨W0, k2, hk2, hW0⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV (k0 (k1 j)) 0).toLp (V (k0 (k1 j)) 0))
    (fun j => hVNorm (k0 (k1 j)) 0)
  obtain ⟨W1, k3, hk3, hW1⟩ := m64SeparableHilbert_weak_subsequence
    (fun j => (hV (k0 (k1 (k2 j))) 1).toLp (V (k0 (k1 (k2 j))) 1))
    (fun j => hVNorm (k0 (k1 (k2 j))) 1)
  let k' := k0 ∘ k1 ∘ k2 ∘ k3
  have hU' : WeakConverges (fun j => (hu (k' j)).toLp (u (k' j))) U :=
    fun L => ((hU L).comp hk2.tendsto_atTop).comp hk3.tendsto_atTop
  have hZ' : Tendsto (fun j => (hF (k' j)).toLp (fun p => rho p * u (k' j) p))
      atTop (𝓝 Z) := ((hZ.comp hk1.tendsto_atTop).comp hk2.tendsto_atTop).comp hk3.tendsto_atTop
  obtain ⟨k4, hk4, hae⟩ := weighted_strong_weak_ae_subsequence
    (fun j => u (k' j)) (fun j => hu (k' j)) rho hrho.continuous hpos h01
    (fun j => hF (k' j)) hU' hZ'
  let k := k' ∘ k4
  let W : Fin 2 → Lp ℝ 2 mu := ![W0, W1]
  have huf : WeakConverges (fun j => (hu (k j)).toLp (u (k j))) U :=
    fun L => (hU' L).comp hk4.tendsto_atTop
  have hVf (i : Fin 2) :
      WeakConverges (fun j => (hV (k j) i).toLp (V (k j) i)) (W i) := by
    fin_cases i
    · intro L
      exact ((hW0 L).comp hk3.tendsto_atTop).comp hk4.tendsto_atTop
    · intro L
      exact (hW1 L).comp hk4.tendsto_atTop
  refine ⟨k, U, W, (hk0.comp (hk1.comp (hk2.comp hk3))).comp hk4, huf, hVf, hae, ?_⟩
  intro i phi hphi hc hs
  let dphi := fun p : LoopPlane => fderiv ℝ phi p (EuclideanSpace.single i 1)
  have hp : MemLp phi 2 mu :=
    (hphi.continuous.memLp_of_hasCompactSupport hc).mono_measure Measure.restrict_le_self
  have hdp : MemLp dphi 2 mu :=
    (((hphi.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hc.fderiv_apply ℝ _)).mono_measure Measure.restrict_le_self
  have hid := weak_limit_linear_identity (hVf i) huf
    (testIntegral (F := ℝ) dphi hdp) (testIntegral phi hp) (fun j => by
      simpa only [testIntegral_toLp, dphi, smul_eq_mul, mul_comm] using hw (k j) i phi hphi hc hs)
  simpa only [testIntegral_apply, dphi, smul_eq_mul, mul_comm] using hid

end PoincareConjecture
