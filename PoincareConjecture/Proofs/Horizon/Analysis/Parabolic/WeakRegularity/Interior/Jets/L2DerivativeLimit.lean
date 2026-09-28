import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.WeakDerivativeLimit
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.WeakRegularity.Interior.Energy.L2Approximation

open Set Filter MeasureTheory
open Poincare.Analysis.Convolution
open scoped ContDiff Topology ENNReal

noncomputable section

namespace Poincare.Analysis.Parabolic.WeakRegularity.Interior

open Poincare.Analysis.Sobolev.WeakCompactness
open Poincare.Analysis.Sobolev.WeakCompactness
open Canonical

local instance {n : ℕ} : Measure.IsAddHaarMeasure (volume : Measure (Spacetime n)) := by
  change ((volume : Measure (Euclid n)).prod (volume : Measure ℝ)).IsAddHaarMeasure
  infer_instance

theorem weak_derivatives_of_strong_l2_limit
    {n : ℕ} {s : Set (Spacetime n)} (hs : IsOpen s)
    {f : Spacetime n → ℝ} (hf : MemLp f 2 (volume.restrict s))
    (u : ℕ → Spacetime n → ℝ) (hu : ∀ m, ContDiffOn ℝ 1 (u m) s)
    {ι : Type*} [Fintype ι] (b : ι → Spacetime n)
    (hU : ∀ m, MemLp (u m) 2 (volume.restrict s))
    (hV : ∀ m i, MemLp
      (fun z => fderiv ℝ (u m) z (b i)) 2 (volume.restrict s))
    (hlim : Tendsto (fun m => (hU m).toLp (u m)) atTop (𝓝 (hf.toLp f)))
    {B : ℝ} (hB : ∀ m, (∑ i, ‖(hV m i).toLp
      (fun z => fderiv ℝ (u m) z (b i))‖ ^ 2) ≤ B) :
    ∃ V : ι → Lp ℝ 2 (volume.restrict s), ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ i, WeakConverges
        (fun m => (hV (k m) i).toLp
          (fun z => fderiv ℝ (u (k m)) z (b i))) (V i)) ∧
      (∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ s →
        (∫ z in s, phi z • V i z) = -(∫ z in s, fderiv ℝ phi z (b i) • f z)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ liminf
        (fun m => ∑ i, ‖(hV (k m) i).toLp
          (fun z => fderiv ℝ (u (k m)) z (b i))‖ ^ 2) atTop ∧
      (∑ i, ‖V i‖ ^ 2) ≤ B := by
  obtain ⟨A, hA⟩ := (Metric.isBounded_range_of_tendsto _ hlim).exists_norm_le
  obtain ⟨u₀, V, k, hk, hu₀, hVv, hdist, hliminf, henergy⟩ :=
    weak_w12_subsequence_spacetime hs u hu b hU hV
      (fun m => hA _ (mem_range_self m)) hB
  have hu₀f : u₀ = hf.toLp f :=
    eq_of_strong_and_weak_limit (hlim.comp hk.tendsto_atTop) hu₀
  refine ⟨V, k, hk, hVv, ?_, hliminf, henergy⟩
  intro i phi hphi hc hsub
  rw [hdist i phi hphi hc hsub, hu₀f]
  congr 1
  exact integral_congr_ae (hf.coeFn_toLp.mono fun z hz =>
    congrArg (fun y => fderiv ℝ phi z (b i) • y) hz)

private theorem tendsto_toLp_restrict
    {n : ℕ} (s : Set (Spacetime n)) {f : Spacetime n → ℝ} (hf : MemLp f 2 volume)
    {u : ℕ → Spacetime n → ℝ} (hU : ∀ m, MemLp (u m) 2 volume)
    (hlim : Tendsto (fun m => (hU m).toLp (u m)) atTop (𝓝 (hf.toLp f))) :
    Tendsto (fun m => ((hU m).restrict s).toLp (u m)) atTop
      (𝓝 ((hf.restrict s).toLp f)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [(Metric.tendsto_nhds.mp hlim) ε hε] with m hm
  have hnorm := ENNReal.toReal_mono ((hU m).sub hf).eLpNorm_ne_top
    (eLpNorm_mono_measure (u m - f) (Measure.restrict_le_self (s := s)))
  have hdist : dist (((hU m).restrict s).toLp (u m)) ((hf.restrict s).toLp f) ≤
      dist ((hU m).toLp (u m)) (hf.toLp f) := by
    simpa only [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp] using hnorm
  exact hdist.trans_lt hm

theorem weak_derivatives_of_mollified_l2_bound
    {n : ℕ} {s : Set (Spacetime n)} (hs : IsOpen s)
    {u ρ : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hmass : (∫ y, ρ y) = 1) {r : ℕ → ℝ} (hr : ∀ m, 0 < r m)
    (hrlim : Tendsto r atTop (𝓝 0))
    {ι : Type*} [Fintype ι] (b : ι → Spacetime n)
    (hV : ∀ m i, MemLp
      (fun z => fderiv ℝ (mollifiedValue u ρ (r m)) z (b i)) 2 (volume.restrict s))
    {B : ℝ} (hB : ∀ m, (∑ i, ‖(hV m i).toLp
      (fun z => fderiv ℝ (mollifiedValue u ρ (r m)) z (b i))‖ ^ 2) ≤ B) :
    ∃ V : ι → Lp ℝ 2 (volume.restrict s), ∃ k : ℕ → ℕ, StrictMono k ∧
      (∀ i, WeakConverges
        (fun m => (hV (k m) i).toLp
          (fun z => fderiv ℝ (mollifiedValue u ρ (r (k m))) z (b i))) (V i)) ∧
      (∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ s →
        (∫ z in s, phi z • V i z) = -(∫ z in s, fderiv ℝ phi z (b i) • u z)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ liminf
        (fun m => ∑ i, ‖(hV (k m) i).toLp
          (fun z => fderiv ℝ (mollifiedValue u ρ (r (k m))) z (b i))‖ ^ 2) atTop ∧
      (∑ i, ‖V i‖ ^ 2) ≤ B := by
  obtain ⟨hU, hlim⟩ := tendsto_mollifiedValue_toLp hu hρ hρc hmass hr hrlim
  have hsmooth (m : ℕ) : ContDiffOn ℝ 1 (mollifiedValue u ρ (r m)) s := by
    have hsm : ContDiff ℝ ∞ (mollifiedValue u ρ (r m)) := by
      apply contDiff_lebesgueConvolution (hu.locallyIntegrable (by norm_num))
      · exact contDiff_const.mul (hρ.comp (contDiff_id.const_smul (r m)⁻¹))
      · exact (hρc.comp_homeomorph
          (Homeomorph.smul (Units.mk0 (r m)⁻¹ (inv_ne_zero (hr m).ne')))).mul_left
    exact (hsm.of_le (by norm_num)).contDiffOn
  exact weak_derivatives_of_strong_l2_limit hs (hu.restrict s)
    (fun m => mollifiedValue u ρ (r m)) hsmooth b (fun m => (hU m).restrict s) hV
    (tendsto_toLp_restrict s hu hU hlim) hB

theorem memLp_fderiv_mollifiedValue
    {n : ℕ} {u ρ : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    {r : ℝ} (hr : 0 < r) (v : Spacetime n) :
    MemLp (fun z => fderiv ℝ (mollifiedValue u ρ r) z v) 2 volume := by
  have hscale : ContDiff ℝ ∞ (rescaledKernel ρ r) :=
    contDiff_const.mul (hρ.comp (contDiff_id.const_smul r⁻¹))
  have hcompact : HasCompactSupport (rescaledKernel ρ r) :=
    (hρc.comp_homeomorph
      (Homeomorph.smul (Units.mk0 r⁻¹ (inv_ne_zero hr.ne')))).mul_left
  have he : (fun z => fderiv ℝ (mollifiedValue u ρ r) z v) =
      lebesgueConvolution (fun y => fderiv ℝ (rescaledKernel ρ r) y v) u := by
    funext z
    exact fderiv_lebesgueConvolution (hu.locallyIntegrable (by norm_num)) hscale hcompact z v
  rw [he]
  exact memLp_lebesgueConvolution hu
    ((hscale.continuous_fderiv (by norm_num)).clm_apply continuous_const)
    (hcompact.fderiv_apply ℝ v)

theorem exists_weak_derivatives_of_mollified_l2_energy
    {n : ℕ} {s : Set (Spacetime n)} (hs : IsOpen s)
    {u ρ : Spacetime n → ℝ} (hu : MemLp u 2 volume)
    (hρ : ContDiff ℝ ∞ ρ) (hρc : HasCompactSupport ρ)
    (hmass : (∫ y, ρ y) = 1) {r : ℕ → ℝ} (hr : ∀ m, 0 < r m)
    (hrlim : Tendsto r atTop (𝓝 0))
    {ι : Type*} [Fintype ι] (b : ι → Spacetime n)
    {B : ℝ} (hB : ∀ m, (∫ z in s,
      ∑ i, (fderiv ℝ (mollifiedValue u ρ (r m)) z (b i)) ^ 2) ≤ B) :
    ∃ V : ι → Lp ℝ 2 (volume.restrict s),
      (∀ i (phi : Spacetime n → ℝ), ContDiff ℝ ∞ phi → HasCompactSupport phi →
        tsupport phi ⊆ s →
        (∫ z in s, phi z • V i z) = -(∫ z in s, fderiv ℝ phi z (b i) • u z)) ∧
      (∑ i, ‖V i‖ ^ 2) ≤ B := by
  have hV (m : ℕ) (i : ι) : MemLp
      (fun z => fderiv ℝ (mollifiedValue u ρ (r m)) z (b i)) 2 (volume.restrict s) :=
    (memLp_fderiv_mollifiedValue hu hρ hρc (hr m) (b i)).restrict s
  have hnorm (m : ℕ) (i : ι) :
      ‖(hV m i).toLp (fun z => fderiv ℝ (mollifiedValue u ρ (r m)) z (b i))‖ ^ 2 =
        ∫ z in s, (fderiv ℝ (mollifiedValue u ρ (r m)) z (b i)) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [(hV m i).coeFn_toLp] with z hz
    simp [hz, pow_two]
  have hB' (m : ℕ) : (∑ i, ‖(hV m i).toLp
      (fun z => fderiv ℝ (mollifiedValue u ρ (r m)) z (b i))‖ ^ 2) ≤ B := by
    simp_rw [hnorm]
    rw [← integral_finsetSum _ (fun i _ => (hV m i).integrable_sq)]
    exact hB m
  obtain ⟨V, k, hk, hweak, hdist, hlow, hbound⟩ :=
    weak_derivatives_of_mollified_l2_bound hs hu hρ hρc hmass hr hrlim b hV hB'
  exact ⟨V, hdist, hbound⟩

end Poincare.Analysis.Parabolic.WeakRegularity.Interior
