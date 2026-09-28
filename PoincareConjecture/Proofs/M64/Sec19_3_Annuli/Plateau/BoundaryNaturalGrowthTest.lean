import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryZeroTraceApproximation
import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.AnnulusSeamSobolevTests
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalWeakTest

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal

namespace PoincareConjecture

open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergDiffQuotTestFunction

set_option maxHeartbeats 900000 in

theorem m64NaturalGrowth_zero_boundary_test
    {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hu : Continuous u) (hc : HasCompactSupport u) (hs : tsupport u ⊆ O)
    (hup : MemLp u 2 volume) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hw : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O ∩ {p : LoopPlane | 0 < p 1} →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p) :
    (∫ p, ∑ i : Fin 2, F i p * du i p) = ∫ p, b p * u p := by
  let H : Set LoopPlane := {p | 0 < p 1}
  have hH : IsOpen H := isOpen_lt continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous
  obtain ⟨eta, heta, hmargin⟩ := hc.isCompact.exists_cthickening_subset_open hO hs
  let delta := fun j : ℕ => min eta (1 / ((j : ℝ) + 1)) / 2
  let v := fun j : ℕ => delta j • EuclideanSpace.single (1 : Fin 2) (1 : ℝ)
  let f := fun j : ℕ => fun p : LoopPlane => u (p - v j)
  let df := fun (j : ℕ) (i : Fin 2) => fun p : LoopPlane => du i (p - v j)
  have hd (j : ℕ) : 0 < delta j := by dsimp [delta]; positivity
  have hde (j : ℕ) : delta j ≤ eta := by
    dsimp [delta]
    linarith [min_le_left eta (1 / ((j : ℝ) + 1))]
  have hv : Tendsto v atTop (𝓝 (0 : LoopPlane)) := by
    have hdelta : Tendsto delta atTop (𝓝 (0 : ℝ)) := by
      have h := ((tendsto_const_nhds (x := eta)).min
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).div_const 2
      simpa only [min_eq_right heta.le, zero_div] using h
    simpa only [zero_smul] using hdelta.smul_const (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
  have hm (j : ℕ) : MeasurePreserving (fun p : LoopPlane => p - v j) volume volume := by
    simpa only [sub_eq_add_neg] using
      measurePreserving_add_right (volume : Measure LoopPlane) (-v j)
  have hfp (j : ℕ) : MemLp (f j) 2 volume := hup.comp_measurePreserving (hm j)
  have hdfp (j : ℕ) (i : Fin 2) : MemLp (df j i) 2 volume :=
    (hdu i).comp_measurePreserving (hm j)
  have hfc (j : ℕ) : HasCompactSupport (f j) := by
    have h := hc.comp_homeomorph (Homeomorph.addRight (-v j))
    change HasCompactSupport (fun p => u (p + (-v j))) at h
    simpa only [f, sub_eq_add_neg] using h
  have hweak (j : ℕ) (i : Fin 2) : HasWeakPartialDeriv i (df j i) (f j) univ := by
    have h := hasWeakPartialDeriv_translate 1 i (delta j) (hw i)
    change HasWeakPartialDeriv i
      (fun p => du i (p + (-delta j) • EuclideanSpace.single (1 : Fin 2) 1))
      (fun p => u (p + (-delta j) • EuclideanSpace.single (1 : Fin 2) 1)) univ at h
    simpa only [df, f, v, neg_smul, ← sub_eq_add_neg] using h
  have hs0 : tsupport u ⊆ {p : LoopPlane | 0 ≤ p 1} := by
    apply closure_minimal ?_
      (isClosed_le continuous_const (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous)
    intro p hp
    exact le_of_not_gt fun hneg => hp (hzero p hneg)
  have hfs (j : ℕ) : tsupport (f j) ⊆ O ∩ H := by
    intro p hp
    have hp' : p - v j ∈ tsupport u :=
      tsupport_comp_subset_preimage u (continuous_id.sub continuous_const) hp
    have hdist : dist p (p - v j) = delta j := by
      rw [dist_eq_norm, sub_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos (hd j)]
      simp
    refine ⟨hmargin (mem_cthickening_of_dist_le p (p - v j) eta (tsupport u) hp'
      (by rw [hdist]; exact hde j)), ?_⟩
    have hn := hs0 hp'
    have hcoord : (p - v j) 1 = p 1 - delta j := by simp [v]
    change 0 ≤ (p - v j) 1 at hn
    rw [hcoord] at hn
    change 0 < p 1
    linarith [hd j]
  have heach (j : ℕ) : (∫ p, ∑ i : Fin 2, F i p * df j i p) = ∫ p, b p * f j p :=
    M60.suNaturalGrowth_weak_test (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
      (hO.inter hH) hF hb (hu.comp (continuous_id.sub continuous_const))
      (hfc j) (hfs j) (hfp j) (hdfp j) (hweak j) heq
  have hflux (i : Fin 2) : Tendsto (fun j => ∫ p, F i p * df j i p) atTop
      (𝓝 (∫ p, F i p * du i p)) := by
    apply m64L2_pairing_tendsto_of_eLpNorm (fun j => hdfp j i) (hdu i) (hF i)
    exact (tendsto_eLpNorm_translate_sub_of_memLp
      (by norm_num : (1 : ℝ≥0∞) ≤ 2) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (hdu i)).comp hv
  have hleft : Tendsto (fun j => ∫ p, ∑ i : Fin 2, F i p * df j i p) atTop
      (𝓝 (∫ p, ∑ i : Fin 2, F i p * du i p)) := by
    have hfint (j : ℕ) (i : Fin 2) : Integrable (fun p => F i p * df j i p) :=
      (hF i).integrable_mul (hdfp j i)
    have huint (i : Fin 2) : Integrable (fun p => F i p * du i p) :=
      (hF i).integrable_mul (hdu i)
    simp_rw [integral_finsetSum Finset.univ (fun i _ => hfint _ i),
      integral_finsetSum Finset.univ (fun i _ => huint i)]
    exact tendsto_finsetSum Finset.univ (fun i _ => hflux i)
  obtain ⟨C, hC⟩ := hc.isCompact.exists_bound_of_continuousOn hu.continuousOn
  have hub (p : LoopPlane) : ‖u p‖ ≤ max C 0 := by
    by_cases hp : p ∈ tsupport u
    · exact (hC p hp).trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hp, norm_zero]
      exact le_max_right _ _
  have hright : Tendsto (fun j => ∫ p, b p * f j p) atTop (𝓝 (∫ p, b p * u p)) := by
    apply tendsto_integral_of_dominated_convergence (fun p => ‖b p‖ * max C 0)
    · intro j
      exact hb.aestronglyMeasurable.mul
        (hu.comp (continuous_id.sub continuous_const)).aestronglyMeasurable
    · exact hb.norm.mul_const _
    · intro j
      filter_upwards with p
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hub _) (norm_nonneg _)
    · filter_upwards with p
      have ht : Tendsto (fun j => p - v j) atTop (𝓝 p) := by
        simpa only [sub_zero] using (tendsto_const_nhds (x := p)).sub hv
      exact tendsto_const_nhds.mul (hu.continuousAt.tendsto.comp ht)
  exact tendsto_nhds_unique hleft (by simpa only [heach] using hright)

end PoincareConjecture
