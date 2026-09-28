import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Weak.NonnegativeApproximation
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.EnergyEstimate.TestFunction.Standard
import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalInterface
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.Analysis.InnerProductSpace.Dual

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal Convolution
open Poincare.Analysis.Sobolev
open Poincare.Analysis.Sobolev.Weak Poincare.Analysis.Sobolev.DifferenceQuotient
open Poincare.Analysis.Sobolev.Euclidean
open Poincare.Analysis.Sobolev.NirenbergStandardTest

noncomputable section

namespace PoincareConjecture.M60

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private theorem weak_flux_pairing_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p q : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ q)] [ENNReal.HolderConjugate p q]
    {f v : X → ℝ} {w : ℕ → X → ℝ}
    (hf : MemLp f p μ) (hv : MemLp v q μ) (hw : ∀ j, MemLp (w j) q μ)
    (hlim : Tendsto (fun j => eLpNorm (w j - v) q μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, f x * w j x ∂μ) atTop (𝓝 (∫ x, f x * v x ∂μ)) := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  have heq (a : X → ℝ) (ha : MemLp a q μ) :
      B.lpPairing μ p q (hf.toLp f) (ha.toLp a) = ∫ x, f x * a x ∂μ := by
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, ha.coeFn_toLp] with x hx hy
    simp [B, hx, hy]
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' w hw v hv).mpr hlim
  have h := (B.lpPairing μ p q (hf.toLp f)).continuous.tendsto (hv.toLp v)
  simpa only [Function.comp_def, heq] using h.comp ht

private theorem uniform_mollification
    {v : Plane → ℝ} (hv : Continuous v) (hvc : HasCompactSupport v)
    {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j) (hlim : Tendsto ε atTop (𝓝 0)) :
    TendstoUniformly (fun j => mollifyEps (hε j) v) v atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro a ha
  obtain ⟨d, hd, hdelta⟩ := Metric.uniformContinuous_iff.mp
    (hvc.uniformContinuous_of_continuous hv) (a / 2) (by positivity)
  filter_upwards [hlim.eventually (gt_mem_nhds hd)] with j hj
  intro x
  have hb : dist (mollifyEps (hε j) v x) (v x) ≤ a / 2 := by
    exact ContDiffBump.dist_normed_convolution_le hv.aestronglyMeasurable
      (fun y hy => (hdelta ((show dist y x < ε j from hy).trans hj)).le)
  exact lt_of_le_of_lt (by simpa only [dist_comm] using hb) (by linarith)

private theorem compact_mollification
    {O : Set Plane} (hO : IsOpen O) {v : Plane → ℝ}
    (hv : Continuous v) (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O) :
    ∃ (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j), Tendsto ε atTop (𝓝 0) ∧
      ∀ j, ContDiff ℝ ∞ (mollifyEps (hε j) v) ∧
        HasCompactSupport (mollifyEps (hε j) v) ∧ tsupport (mollifyEps (hε j) v) ⊆ O := by
  obtain ⟨δ, hδ, hδO⟩ := hvc.isCompact.exists_cthickening_subset_open hO hvO
  let ε : ℕ → ℝ := fun j => min δ (1 / (j + 1 : ℝ))
  have hε : ∀ j, 0 < ε j := fun j => lt_min hδ (by positivity)
  refine ⟨ε, hε, ?_, fun j => ?_⟩
  · have h := (tendsto_const_nhds (x := δ)).min
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
    simpa only [min_eq_right hδ.le] using h
  · have he : mollifyEps (hε j) v =
        v ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] mollifierEps (hε j) := by
      funext x
      rw [mollifyEps, convolution_lsmul, convolution_lsmul_swap]
      exact integral_congr_ae <| Eventually.of_forall fun y => by simp only [smul_eq_mul, mul_comm]
    have hs : tsupport (mollifyEps (hε j) v) ⊆ cthickening δ (tsupport v) := by
      rw [he]
      exact (tsupport_convolution_mollifierEps_subset_thickening (hε j)).trans
        (cthickening_mono (min_le_left _ _) _)
    exact ⟨mollifyEps_contDiff (hε j) hv.locallyIntegrable,
      (hvc.isCompact.cthickening (r := δ)).of_isClosed_subset (isClosed_tsupport _) hs,
      hs.trans hδO⟩

theorem suNaturalGrowth_weak_test
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) (hq : 1 ≤ q)
    [ENNReal.HolderConjugate q p]
    {O : Set Plane} (hO : IsOpen O)
    {F : Fin 2 → Plane → ℝ} {b v : Plane → ℝ} {dv : Fin 2 → Plane → ℝ}
    (hF : ∀ i, MemLp (F i) q volume) (hb : Integrable b)
    (hv : Continuous v) (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O)
    (hvp : MemLp v p volume) (hdv : ∀ i, MemLp (dv i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (dv i) v univ)
    (heq : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, ∑ i : Fin 2, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, b x * φ x) :
    (∫ x, ∑ i : Fin 2, F i x * dv i x) = ∫ x, b x * v x := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Fact (1 ≤ q) := ⟨hq⟩
  obtain ⟨ε, hε, hεlim, hprops⟩ := compact_mollification hO hv hvc hvO
  let φ : ℕ → Plane → ℝ := fun j => mollifyEps (hε j) v
  have hφ (j) : ContDiff ℝ ∞ (φ j) := (hprops j).1
  have hφc (j) : HasCompactSupport (φ j) := (hprops j).2.1
  have hdφ (j) (i : Fin 2) :
      MemLp (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) p volume :=
    (((hφ j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport ((hφc j).fderiv_apply (𝕜 := ℝ) _)
  have hleft (i : Fin 2) : Tendsto
      (fun j => ∫ x, F i x * fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) atTop
      (𝓝 (∫ x, F i x * dv i x)) := by
    apply weak_flux_pairing_tendsto (hF i) (hdv i) (fun j => hdφ j i)
    exact tendsto_eLpNorm_mollifyEps_partial_sub hε hεlim hp hpfin
      (hvp.locallyIntegrable hp) (hdv i) (hweak i)
  have hsum : Tendsto
      (fun j => ∫ x, ∑ i : Fin 2, F i x * fderiv ℝ (φ j) x (EuclideanSpace.single i 1))
      atTop (𝓝 (∫ x, ∑ i : Fin 2, F i x * dv i x)) := by
    simp_rw [integral_finsetSum Finset.univ (fun i _ =>
      memLp_one_iff_integrable.mp ((hdv i).mul' (hF i)))]
    convert tendsto_finsetSum Finset.univ (fun i _ => hleft i) using 1
    funext j
    exact integral_finsetSum Finset.univ (fun i _ =>
      memLp_one_iff_integrable.mp ((hdφ j i).mul' (hF i)))
  have hunif : TendstoUniformly φ v atTop := uniform_mollification hv hvc hε hεlim
  have hvtop : MemLp v ⊤ volume := hv.memLp_of_hasCompactSupport hvc
  have hφtop (j) : MemLp (φ j) ⊤ volume :=
    (hφ j).continuous.memLp_of_hasCompactSupport (hφc j)
  have htop : Tendsto (fun j => eLpNorm (φ j - v) ⊤ volume) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro a ha
    obtain ⟨r, _, hr, hra⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
    have hrpos : 0 < r := ENNReal.ofReal_pos.mp hr
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif r hrpos] with j hj
    rw [eLpNorm_exponent_top]
    apply (eLpNormEssSup_le_of_ae_bound
      (Eventually.of_forall fun x => ?_)).trans hra.le
    simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (hj x).le
  have hright := weak_flux_pairing_tendsto
    (memLp_one_iff_integrable.mpr hb) hvtop hφtop htop
  exact tendsto_nhds_unique hsum (by
    simpa only [heq _ (hφ _) (hφc _) (hprops _).2.2] using hright)

theorem suNaturalGrowth_cutoff_test
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) (hq : 1 ≤ q)
    [ENNReal.HolderConjugate q p]
    {O : Set Plane} (hO : IsOpen O)
    {F : Fin 2 → Plane → ℝ} {b u ξ : Plane → ℝ} {du : Fin 2 → Plane → ℝ}
    (hF : ∀ i, MemLp (F i) q volume) (hb : Integrable b)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξO : tsupport ξ ⊆ O)
    (heq : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, ∑ i : Fin 2, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, b x * φ x) :
    (∫ x, ∑ i : Fin 2, F i x *
      (ξ x ^ 2 * du i x + 2 * ξ x *
        fderiv ℝ ξ x (EuclideanSpace.single i 1) * u x)) =
      ∫ x, b x * (ξ x ^ 2 * u x) := by
  let η : Plane → ℝ := fun x => ξ x ^ 2
  have hη : ContDiff ℝ ∞ η := hξ.pow 2
  have hηsupp : tsupport η ⊆ tsupport ξ := by
    exact tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) ξ
  have hηc : HasCompactSupport η :=
    hξc.of_isClosed_subset (isClosed_tsupport η) hηsupp
  have hηtop : MemLp η ⊤ volume := hη.continuous.memLp_of_hasCompactSupport hηc
  have hdη (i : Fin 2) (x : Plane) :
      fderiv ℝ η x (EuclideanSpace.single i 1) =
        2 * ξ x * fderiv ℝ ξ x (EuclideanSpace.single i 1) := by
    rw [show η = fun x => ξ x ^ 2 from rfl,
      fderiv_fun_pow 2 (hξ.differentiable (by simp) x)]
    simp only [Nat.add_one_sub_one, pow_one, smul_apply, smul_eq_mul,
      nsmul_eq_mul, Nat.cast_ofNat]
  have ht := suNaturalGrowth_weak_test hp hpfin hq hO hF hb
    (hη.continuous.mul hu) hηc.mul_right
    (tsupport_mul_subset_left.trans (hηsupp.trans hξO))
    ((hη.continuous.mul hu).memLp_of_hasCompactSupport hηc.mul_right)
    (fun i => ((hdu i).mul' hηtop).add
      ((((hη.continuous_fderiv (by simp)).clm_apply continuous_const).mul hu
        ).memLp_of_hasCompactSupport ((hηc.fderiv_apply (𝕜 := ℝ) _).mul_right)))
    (fun i => (hweak i).mul_smooth isOpen_univ hη
      (by simpa using hu.locallyIntegrable)
      (by simpa using (hdu i).locallyIntegrable hp)) heq
  simpa only [η, hdη, Pi.add_apply, Pi.mul_apply] using ht

theorem suWeakMap_diffQuot_memLp
    {p : ℝ≥0∞} {f : Plane → ℝ} (hf : MemLp f p volume) (k : Fin 2) (h : ℝ) :
    MemLp (diffQuot k h f) p volume := by
  by_cases hh : h = 0
  · simpa only [hh, diffQuot_zero_h] using (MemLp.zero (p := p) (μ := (volume : Measure Plane)))
  · rw [diffQuot_eq_translate_sub_div k hh]
    simpa only [Pi.sub_apply, div_eq_mul_inv, mul_comm] using
      ((memLp_translate k h hf).sub hf).const_mul h⁻¹

private theorem naturalGrowth_diffQuot_pairing
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate q p]
    {f v : Plane → ℝ} (hf : MemLp f q volume) (hv : MemLp v p volume)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0) :
    (∫ x, diffQuot k h f x * v x) = -(∫ x, f x * diffQuot k (-h) v x) := by
  have hfv : Integrable (fun x => f x * v x) :=
    memLp_one_iff_integrable.mp (hv.mul' hf)
  have htv : Integrable (fun x => translate k h f x * v x) :=
    memLp_one_iff_integrable.mp (hv.mul' (memLp_translate k h hf))
  have hft : Integrable (fun x => f x * translate k (-h) v x) :=
    memLp_one_iff_integrable.mp ((memLp_translate k (-h) hv).mul' hf)
  have ht : (∫ x, translate k h f x * v x) = ∫ x, f x * translate k (-h) v x := by
    have he := integral_add_right_eq_self
      (μ := (volume : Measure Plane))
      (fun x : Plane => f (x + h • EuclideanSpace.single k 1) * v x)
      ((-h) • EuclideanSpace.single k 1)
    simpa only [Poincare.Analysis.Sobolev.translate, neg_smul,
      add_assoc, neg_add_cancel, add_zero] using he.symm
  have hL : (fun x => diffQuot k h f x * v x) =
      fun x => (translate k h f x * v x - f x * v x) / h := by
    funext x
    rw [diffQuot_apply_of_ne k hh]
    dsimp only [Poincare.Analysis.Sobolev.translate]
    ring
  have hR : (fun x => f x * diffQuot k (-h) v x) =
      fun x => (f x * translate k (-h) v x - f x * v x) / (-h) := by
    funext x
    rw [diffQuot_apply_of_ne k (neg_ne_zero.mpr hh)]
    dsimp only [Poincare.Analysis.Sobolev.translate]
    ring
  rw [hL, hR, integral_div, integral_div, integral_sub htv hfv,
    integral_sub hft hfv, ht, div_neg, neg_neg]

theorem suNaturalGrowth_nirenberg_identity
    {p q : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) (hq : 1 ≤ q)
    [ENNReal.HolderConjugate q p]
    {O : Set Plane} (hO : IsOpen O)
    {F du : Fin 2 → Plane → ℝ} {b u ξ : Plane → ℝ}
    (hF : ∀ i, MemLp (F i) q volume) (hb : Integrable b)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ)
    (heq : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, ∑ i : Fin 2, F i x * fderiv ℝ φ x (EuclideanSpace.single i 1)) =
        ∫ x, b x * φ x)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0)
    (hsupp : cthickening |h| (tsupport ξ) ⊆ O) :
    (∫ x, ∑ i : Fin 2, diffQuot k h (F i) x *
      (ξ x ^ 2 * diffQuot k h (du i) x + 2 * ξ x *
        fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x)) =
      ∫ x, diffQuot k h b x * (ξ x ^ 2 * diffQuot k h u x) := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  let : Fact (1 ≤ q) := ⟨hq⟩
  let w : Plane → ℝ := fun x => ξ x ^ 2 * diffQuot k h u x
  let dw (i : Fin 2) (x : Plane) := ξ x ^ 2 * diffQuot k h (du i) x +
    2 * ξ x * fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x
  have huc := continuous_diffQuot_of_continuous k h hu
  have hξ2c : HasCompactSupport (fun x => ξ x ^ 2) :=
    hξc.of_isClosed_subset (isClosed_tsupport _) <|
      tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) ξ
  have hwc : HasCompactSupport w := hξ2c.mul_right
  have hwcont : Continuous w := (hξ.continuous.pow 2).mul huc
  have hdw (i : Fin 2) : MemLp (dw i) p volume := by
    apply ((suWeakMap_diffQuot_memLp (hdu i) k h).mul'
      ((hξ.continuous.pow 2).memLp_of_hasCompactSupport hξ2c : MemLp _ ⊤ volume)).add
    have hc : Continuous (fun x => 2 * ξ x *
        fderiv ℝ ξ x (EuclideanSpace.single i 1) * diffQuot k h u x) :=
      ((continuous_const.mul hξ.continuous).mul
        ((hξ.continuous_fderiv (by simp)).clm_apply continuous_const)).mul huc
    exact hc.memLp_of_hasCompactSupport ((hξc.mul_left.mul_right).mul_right)
  have hvc := standardNirenbergTest_hasCompactSupport k h hξc u
  have hvcont : Continuous (standardNirenbergTest k h ξ u) :=
    continuous_diffQuot_of_continuous k (-h) hwcont
  have hvO : tsupport (standardNirenbergTest k h ξ u) ⊆ O := by
    intro x hx
    apply hsupp
    rcases standardNirenbergTest_tsupport_subset k h u hx with hx | hx
    · exact self_subset_cthickening _ hx
    · apply mem_cthickening_of_dist_le _ (x + (-h) • EuclideanSpace.single k 1) _ _ hx
      simp [dist_eq_norm, norm_smul, Real.norm_eq_abs]
  have ht := suNaturalGrowth_weak_test hp hpfin hq hO hF hb hvcont hvc hvO
    (hvcont.memLp_of_hasCompactSupport hvc)
    (fun i => suWeakMap_diffQuot_memLp (hdw i) k (-h))
    (fun i => hasWeakPartialDeriv_standardNirenbergTest k i h hξ
      (by simpa using hu.locallyIntegrable)
      (by simpa using (hdu i).locallyIntegrable hp) (hweak i)) heq
  have hpair (i : Fin 2) := naturalGrowth_diffQuot_pairing (hF i) (hdw i) k hh
  have hbpair := naturalGrowth_diffQuot_pairing (memLp_one_iff_integrable.mpr hb)
    (hwcont.memLp_of_hasCompactSupport hwc : MemLp w ⊤ volume) k hh
  rw [integral_finsetSum _ (fun i _ => memLp_one_iff_integrable.mp
    ((suWeakMap_diffQuot_memLp (hdw i) k (-h)).mul' (hF i)))] at ht
  rw [integral_finsetSum _ (fun i _ => memLp_one_iff_integrable.mp
    ((hdw i).mul' (suWeakMap_diffQuot_memLp (hF i) k h)))]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpair i)
  rw [Finset.sum_neg_distrib, ht] at hsum
  exact hsum.trans hbpair.symm

private theorem weighted_square_tendsto
    {X : Type*} [MeasurableSpace X] {μ : Measure X} {p r t : ℝ≥0∞}
    [Fact (1 ≤ p)] [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [ENNReal.HolderTriple p p t] [ENNReal.HolderConjugate r t]
    {W v : X → ℝ} {f : ℕ → X → ℝ}
    (hW : MemLp W r μ) (hv : MemLp v p μ) (hf : ∀ j, MemLp (f j) p μ)
    (hlim : Tendsto (fun j => eLpNorm (f j - v) p μ) atTop (𝓝 0)) :
    Tendsto (fun j => ∫ x, W x * f j x ^ 2 ∂μ) atTop
      (𝓝 (∫ x, W x * v x ^ 2 ∂μ)) := by
  let B := ContinuousLinearMap.mul ℝ ℝ
  let C := B.holderL μ p p t
  let L := B.lpPairing μ r t (hW.toLp W)
  have heq (a : X → ℝ) (ha : MemLp a p μ) :
      L (C (ha.toLp a) (ha.toLp a)) = ∫ x, W x * a x ^ 2 ∂μ := by
    rw [show L = B.lpPairing μ r t (hW.toLp W) from rfl,
      ContinuousLinearMap.lpPairing_eq_integral]
    apply integral_congr_ae
    have hc := B.coeFn_holder (r := t) (ha.toLp a) (ha.toLp a)
    filter_upwards [hW.coeFn_toLp, ha.coeFn_toLp, hc] with x hx ha' hc'
    change (hW.toLp W) x * (B.holder t (ha.toLp a) (ha.toLp a)) x = _
    rw [hx, hc']
    simp [B, ha', pow_two]
  have hc : Continuous (fun a : Lp ℝ p μ => L (C a a)) :=
    L.continuous.comp (C.continuous.clm_apply continuous_id)
  have ht := (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf v hv).mpr hlim
  simpa only [Function.comp_def, heq] using hc.tendsto (hv.toLp v) |>.comp ht

theorem suWeightedPotential_weak_bound
    {p r t : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    [Fact (1 ≤ r)] [Fact (1 ≤ t)]
    [ENNReal.HolderTriple p p t] [ENNReal.HolderConjugate r t]
    {O : Set Plane} (hO : IsOpen O)
    {H W v : Plane → ℝ} {dv : Fin 2 → Plane → ℝ} {c : ℝ}
    (hH : Integrable H) (hW : MemLp W r volume)
    (hv : Continuous v) (hvc : HasCompactSupport v) (hvO : tsupport v ⊆ O)
    (hdv : ∀ i, MemLp (dv i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (dv i) v univ)
    (hbound : ∀ φ : Plane → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ O →
      (∫ x, H x * φ x ^ 2) ≤ c *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ φ x (EuclideanSpace.single i 1)) ^ 2) :
    (∫ x, H x * v x ^ 2) ≤ c * ∫ x, W x * ∑ i : Fin 2, dv i x ^ 2 := by
  let : Fact (1 ≤ p) := ⟨hp⟩
  obtain ⟨ε, hε, hεlim, hprops⟩ := compact_mollification hO hv hvc hvO
  let φ : ℕ → Plane → ℝ := fun j => mollifyEps (hε j) v
  have hφ (j) : ContDiff ℝ ∞ (φ j) := (hprops j).1
  have hφc (j) : HasCompactSupport (φ j) := (hprops j).2.1
  have hdφ (j) (i : Fin 2) :
      MemLp (fun x => fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) p volume :=
    (((hφ j).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous
      |>.memLp_of_hasCompactSupport ((hφc j).fderiv_apply (𝕜 := ℝ) _)
  have hdlim (i : Fin 2) := weighted_square_tendsto (t := t) hW (hdv i) (fun j => hdφ j i)
    (tendsto_eLpNorm_mollifyEps_partial_sub hε hεlim hp hpfin
      hv.locallyIntegrable (hdv i) (hweak i))
  have hsum : Tendsto
      (fun j => ∫ x, W x * ∑ i : Fin 2,
        (fderiv ℝ (φ j) x (EuclideanSpace.single i 1)) ^ 2) atTop
      (𝓝 (∫ x, W x * ∑ i : Fin 2, dv i x ^ 2)) := by
    have hi {f : Plane → ℝ} (hf : MemLp f p volume) : Integrable (fun x => W x * f x ^ 2) := by
      have hs : MemLp (fun x => f x ^ 2) t volume := by simpa only [pow_two] using hf.mul' hf
      exact memLp_one_iff_integrable.mp (hs.mul' hW)
    simpa only [Finset.mul_sum, integral_finsetSum _ (fun i _ => hi (hdv i)),
      integral_finsetSum _ (fun i _ => hi (hdφ _ i))] using
      tendsto_finsetSum Finset.univ (fun i _ => hdlim i)
  have hunif := uniform_mollification hv hvc hε hεlim
  have htop : Tendsto (fun j => eLpNorm (φ j - v) ⊤ volume) atTop (𝓝 0) := by
    rw [ENNReal.tendsto_nhds_zero]
    intro a ha
    obtain ⟨s, _, hs, hsa⟩ := ENNReal.lt_iff_exists_real_btwn.mp ha
    filter_upwards [Metric.tendstoUniformly_iff.mp hunif s (ENNReal.ofReal_pos.mp hs)] with j hj
    rw [eLpNorm_exponent_top]
    apply (eLpNormEssSup_le_of_ae_bound (Eventually.of_forall fun x => ?_)).trans hsa.le
    simpa only [Pi.sub_apply, ← dist_eq_norm, dist_comm] using (hj x).le
  have hleft := weighted_square_tendsto (t := ⊤) (memLp_one_iff_integrable.mpr hH)
    (hv.memLp_of_hasCompactSupport hvc : MemLp v ⊤ volume)
    (fun j => (hφ j).continuous.memLp_of_hasCompactSupport (hφc j)) htop
  exact le_of_tendsto_of_tendsto hleft (hsum.const_mul c)
    (Eventually.of_forall fun j => hbound (φ j) (hφ j) (hφc j) (hprops j).2.2)

theorem suWeakMap_diffQuot_bounded
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤)
    {u : Plane → ℝ} {du : Fin 2 → Plane → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u)
    (hdu : ∀ i, MemLp (du i) p volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ (k : Fin 2) (h : ℝ), eLpNorm (diffQuot k h u) p volume ≤ C := by
  obtain ⟨ε, hε, hεlim, hprops⟩ := compact_mollification isOpen_univ hu huc (subset_univ _)
  let φ : ℕ → Plane → ℝ := fun j => mollifyEps (hε j) u
  let d (j : ℕ) (i : Fin 2) (x : Plane) := fderiv ℝ (φ j) x (EuclideanSpace.single i 1)
  have hφ (j) : ContDiff ℝ ∞ (φ j) := (hprops j).1
  have hdc (j) (i : Fin 2) : Continuous (d j i) :=
    ((hφ j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdlim (i : Fin 2) : Tendsto (fun j => eLpNorm (d j i - du i) p volume) atTop (𝓝 0) :=
    tendsto_eLpNorm_mollifyEps_partial_sub hε hεlim hp hpfin hu.locallyIntegrable (hdu i) (hweak i)
  have hdb : ∀ᶠ j in atTop, ∀ i : Fin 2,
      eLpNorm (d j i) p volume ≤ 1 + eLpNorm (du i) p volume := by
    apply eventually_all.mpr
    intro i
    filter_upwards [(hdlim i).eventually (gt_mem_nhds (by norm_num : (0 : ℝ≥0∞) < 1))] with j hj
    calc
      _ = eLpNorm ((d j i - du i) + du i) p volume := by rw [sub_add_cancel]
      _ ≤ eLpNorm (d j i - du i) p volume + eLpNorm (du i) p volume :=
        eLpNorm_add_le ((hdc j i).aestronglyMeasurable.sub (hdu i).1) (hdu i).1 hp
      _ ≤ 1 + eLpNorm (du i) p volume := add_le_add hj.le le_rfl
  let C := (1 + eLpNorm (du 0) p volume) + (1 + eLpNorm (du 1) p volume)
  have hC : C < ⊤ := by
    exact ENNReal.add_lt_top.mpr ⟨ENNReal.add_lt_top.mpr ⟨by simp, (hdu 0).2⟩,
      ENNReal.add_lt_top.mpr ⟨by simp, (hdu 1).2⟩⟩
  have hL (L : Plane →L[ℝ] ℝ) :
      ‖L‖ ≤ |L (EuclideanSpace.single 0 1)| + |L (EuclideanSpace.single 1 1)| := by
    have hsq := (EuclideanSpace.basisFun (Fin 2) ℝ).norm_dual L
    simp only [Fin.sum_univ_two, EuclideanSpace.basisFun_apply] at hsq
    nlinarith [abs_nonneg (L (EuclideanSpace.single 0 1)),
      abs_nonneg (L (EuclideanSpace.single 1 1)), sq_abs (L (EuclideanSpace.single 0 1)),
      sq_abs (L (EuclideanSpace.single 1 1)), norm_nonneg L]
  have hgrad : ∀ᶠ j in atTop, eLpNorm (fun x => ‖fderiv ℝ (φ j) x‖) p volume ≤ C := by
    filter_upwards [hdb] with j hj
    calc
      _ ≤ eLpNorm (fun x => ‖d j 0 x‖ + ‖d j 1 x‖) p volume := by
        apply eLpNorm_mono
        intro x
        rw [norm_norm, Real.norm_of_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _))]
        simpa only [d, Real.norm_eq_abs] using hL (fderiv ℝ (φ j) x)
      _ ≤ eLpNorm (d j 0) p volume + eLpNorm (d j 1) p volume := by
        simpa only [Pi.add_def, eLpNorm_norm] using
          eLpNorm_add_le (hdc j 0).norm.aestronglyMeasurable (hdc j 1).norm.aestronglyMeasurable hp
      _ ≤ C := add_le_add (hj 0) (hj 1)
  refine ⟨C, hC, fun k h => ?_⟩
  by_cases hh : h = 0
  · simp [hh]
  have hbound : ∀ᶠ j in atTop, eLpNorm (diffQuot k h (φ j)) p volume ≤ C := by
    filter_upwards [hgrad] with j hj
    have ht := eLpNorm_translate_sub_le_smul_eLpNorm_fderiv hp hpfin (hφ j)
      ((-h) • EuclideanSpace.single k 1)
    have he : (fun x => φ j x - φ j (x - (-h) • EuclideanSpace.single k 1)) =
        (-h) • diffQuot k h (φ j) := by
      funext x
      simp only [Pi.smul_apply, smul_eq_mul, neg_smul, sub_neg_eq_add,
        diffQuot_apply_of_ne k hh]
      field_simp
      ring
    rw [he, eLpNorm_const_smul] at ht
    have ht' : ENNReal.ofReal |h| * eLpNorm (diffQuot k h (φ j)) p volume ≤
        ENNReal.ofReal |h| * eLpNorm (fun x => ‖fderiv ℝ (φ j) x‖) p volume := by
      simpa only [norm_smul, norm_neg, Real.norm_eq_abs, PiLp.norm_single,
        norm_one, mul_one, enorm_neg, ← ofReal_norm] using ht
    exact ((ENNReal.mul_le_mul_iff_right
      (ENNReal.ofReal_pos.mpr (abs_pos.mpr hh)).ne' ENNReal.ofReal_ne_top).mp ht').trans hj
  apply Lp.eLpNorm_le_of_ae_tendsto hbound
    (fun j => (continuous_diffQuot_of_continuous k h (hφ j).continuous).aestronglyMeasurable)
  have ht := (uniform_mollification hu huc hε hεlim).tendsto_at
  exact Eventually.of_forall fun x => by
    simp only [diffQuot_apply_of_ne k hh]
    exact ((ht _).sub (ht _)).div_const h

theorem suWeakMap_compact_cutoff
    {O : Set Plane} (hO : IsOpen O) {p : ℝ} (hp : 1 < p)
    {u ξ : Plane → ℝ} {du : Fin 2 → Plane → ℝ}
    (hu : ContinuousOn u O) (hup : MemLp u (ENNReal.ofReal p) (volume.restrict O))
    (hdu : ∀ i, MemLp (du i) (ENNReal.ofReal p) (volume.restrict O))
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u O)
    (hξ : ContDiff ℝ ∞ ξ) (hξc : HasCompactSupport ξ) (hξO : tsupport ξ ⊆ O) :
    Continuous (fun x => ξ x * u x) ∧ HasCompactSupport (fun x => ξ x * u x) ∧
      MemLp (fun x => ξ x * u x) (ENNReal.ofReal p) volume ∧
      ∀ i, MemLp (fun x => ξ x * du i x +
          fderiv ℝ ξ x (EuclideanSpace.single i 1) * u x) (ENNReal.ofReal p) volume ∧
        HasWeakPartialDeriv i
          (fun x => ξ x * du i x + fderiv ℝ ξ x (EuclideanSpace.single i 1) * u x)
          (fun x => ξ x * u x) univ := by
  classical
  let v (x : Plane) := ξ x * u x
  let dv (i : Fin 2) (x : Plane) :=
    ξ x * du i x + fderiv ℝ ξ x (EuclideanSpace.single i 1) * u x
  have hvO : tsupport v ⊆ O := tsupport_mul_subset_left.trans hξO
  have hv : Continuous v :=
    (hξ.continuous.continuousOn.mul hu).continuous_of_tsupport_subset hO hvO
  have hvc : HasCompactSupport v := hξc.mul_right
  have hp1 : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_of_lt hp)
  have hξtop : MemLp ξ ⊤ (volume.restrict O) :=
    (hξ.continuous.memLp_of_hasCompactSupport hξc).restrict O
  have hdv (i : Fin 2) : MemLp (dv i) (ENNReal.ofReal p) (volume.restrict O) := by
    have hdξ : MemLp (fun x => fderiv ℝ ξ x (EuclideanSpace.single i 1)) ⊤
        (volume.restrict O) :=
      (((hξ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_of_hasCompactSupport
        (hξc.fderiv_apply (𝕜 := ℝ) _)).restrict O
    exact ((hdu i).mul' hξtop).add (hup.mul' hdξ)
  let hw : MemW1pWitness (ENNReal.ofReal p) v O :=
    { memLp := (hv.memLp_of_hasCompactSupport hvc).restrict O
      weakGrad := fun x => WithLp.toLp 2 (fun i => dv i x)
      weakGrad_component_memLp := hdv
      isWeakGrad := fun i => (hweak i).mul_smooth hO hξ
        (hup.locallyIntegrable hp1) ((hdu i).locallyIntegrable hp1) }
  have hw0 := memW01p_of_memW1p_of_tsupport_subset hO hp
    (show MemW1p (ENNReal.ofReal p) v O from
      ⟨hw.memLp, fun i => ⟨dv i, hdv i, hw.isWeakGrad i⟩⟩) hvc hvO
  let hext := zeroExtendMemW1pWitnessP hO hp hw0 hw
  have hvind : O.indicator v = v := by
    exact indicator_eq_self.mpr (subset_tsupport v |>.trans hvO)
  have hdvind (i : Fin 2) : O.indicator (dv i) = dv i := by
    apply indicator_eq_self.mpr
    intro x hx
    by_contra hxO
    have hξ0 : ξ x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hxO (hξO h))
    have hdξ0 : fderiv ℝ ξ x (EuclideanSpace.single i 1) = 0 :=
      image_eq_zero_of_notMem_tsupport
        (f := fun y => fderiv ℝ ξ y (EuclideanSpace.single i 1)) (fun h => hxO
        (((tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i (1 : ℝ))).trans hξO) h))
    exact hx (by simp only [dv, hξ0, hdξ0, zero_mul, add_zero])
  refine ⟨hv, hvc, hv.memLp_of_hasCompactSupport hvc, fun i => ⟨?_, ?_⟩⟩
  · simpa only [hext, zeroExtendMemW1pWitnessP, PiLp.toLp_apply, hw,
      hdvind, Measure.restrict_univ] using hext.weakGrad_component_memLp i
  · simpa only [hext, zeroExtendMemW1pWitnessP, PiLp.toLp_apply, hw,
      hdvind, hvind] using hext.isWeakGrad i

theorem suWeakMap_sub_const {O : Set Plane} (hO : IsOpen O)
    {u v : Plane → ℝ} {i : Fin 2}
    (hu : LocallyIntegrable u (volume.restrict O))
    (hweak : HasWeakPartialDeriv i v u O) (c : ℝ) :
    HasWeakPartialDeriv i v (fun x => u x - c) O := by
  intro phi hphi hc hsupport
  have hderiv := (hphi.continuous_fderiv (by simp)).clm_apply
    (continuous_const (y := EuclideanSpace.single i (1 : ℝ)))
  have hderivc := hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i (1 : ℝ))
  have hui : Integrable (fun x => u x * fderiv ℝ phi x (EuclideanSpace.single i 1))
      (volume.restrict O) := by
    simpa only [smul_eq_mul] using
      hu.integrable_smul_right_of_hasCompactSupport hderiv hderivc
  have hci : Integrable (fun x => c * fderiv ℝ phi x (EuclideanSpace.single i 1))
      (volume.restrict O) :=
    ((continuous_const.mul hderiv).integrable_of_hasCompactSupport hderivc.mul_left).restrict
  have hconst := HasWeakPartialDeriv.of_contDiff hO
    (i := i) (contDiff_const : ContDiff ℝ 1 (fun _ : Plane => c))
      phi hphi hc hsupport
  simp only [fderiv_const_apply, zero_apply, zero_mul, integral_zero,
    neg_zero] at hconst
  simp_rw [sub_mul]
  rw [integral_sub hui hci, hconst, sub_zero]
  exact hweak phi hphi hc hsupport

def suColumnBasis {m : ℕ} (a : Fin m) (i : Fin 2) :
    EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m) :=
  if i = 0 then (EuclideanSpace.single a 1, 0) else (0, EuclideanSpace.single a 1)

theorem suCoordinateDual_pairing {m : ℕ}
    (L : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ) (v : EuclideanSpace ℝ (Fin m)) :
    (∑ a : Fin m, L (EuclideanSpace.single a 1) * v a) = L v := by
  have hv : (∑ a : Fin m, v a • EuclideanSpace.single a (1 : ℝ)) = v := by
    simpa only [EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply] using
      (EuclideanSpace.basisFun (Fin m) ℝ).sum_repr v
  rw [← hv]
  simp only [map_sum, map_smul, smul_eq_mul]
  rw [hv]
  exact Finset.sum_congr rfl fun a _ => mul_comm _ _

theorem suColumnDual_pairing {m : ℕ}
    (L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
    (v : Fin 2 → EuclideanSpace ℝ (Fin m)) :
    (∑ a : Fin m, ∑ i : Fin 2, L (suColumnBasis a i) * v i a) = L (v 0, v 1) := by
  simp only [Fin.sum_univ_two, Finset.sum_add_distrib, suColumnBasis, ↓reduceIte, one_ne_zero]
  have h0 := suCoordinateDual_pairing
    (L.comp (ContinuousLinearMap.inl ℝ _ _)) (v 0)
  have h1 := suCoordinateDual_pairing
    (L.comp (ContinuousLinearMap.inr ℝ _ _)) (v 1)
  change (∑ a : Fin m, L (EuclideanSpace.single a 1, 0) * v 0 a) = L (v 0, 0) at h0
  change (∑ a : Fin m, L (0, EuclideanSpace.single a 1) * v 1 a) = L (0, v 1) at h1
  rw [h0, h1, ← map_add]
  simp only [Prod.mk_add_mk, add_zero, zero_add]

namespace SUQuadraticWeakSystem

variable {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
  {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}

def componentFlux (S : SUQuadraticWeakSystem u V center R)
    (a : Fin m) (i : Fin 2) (x : LoopPlane) : ℝ :=
  S.flux (x, u x) (V 0 x, V 1 x) (suColumnBasis a i)

def componentSource (S : SUQuadraticWeakSystem u V center R)
    (a : Fin m) (x : LoopPlane) : ℝ :=
  S.source (x, u x) (V 0 x, V 1 x) (EuclideanSpace.single a 1)

theorem base_mem (S : SUQuadraticWeakSystem u V center R)
    {x : LoopPlane} (hx : x ∈ Metric.closedBall center R) :
    (x, u x) ∈ Metric.closedBall center R ×ˢ
      Metric.closedBall (u center) S.targetRadius := by
  exact ⟨hx, (Metric.closedBall_subset_closedBall (by linarith [S.targetRadius_pos]))
    (Metric.ball_subset_closedBall (S.coordinate_range hx))⟩

theorem operator_memLp (S : SUQuadraticWeakSystem u V center R) :
    let mu := volume.restrict (Metric.ball center R)
    MemLp (fun x => S.flux (x, u x) (V 0 x, V 1 x)) 2 mu ∧
      Integrable (fun x => S.source (x, u x) (V 0 x, V 1 x)) mu := by
  classical
  let E := EuclideanSpace ℝ (Fin m)
  let mu := volume.restrict (Metric.ball center R)
  let K := (Metric.closedBall center R ×ˢ Metric.closedBall (u center) S.targetRadius) ×ˢ
    (univ : Set (E × E))
  have hK : MeasurableSet K :=
    (measurableSet_closedBall.prod measurableSet_closedBall).prod MeasurableSet.univ
  let q (x : LoopPlane) := (V 0 x, V 1 x)
  let z (x : LoopPlane) := ((x, u x), q x)
  have hq : MemLp q 2 mu := memLp_prod_iff.mpr ⟨S.column_memLp 0, S.column_memLp 1⟩
  have hz : AEMeasurable z mu :=
    (measurable_id.aemeasurable.prodMk S.coordinate_memLp.1.aemeasurable).prodMk
      hq.1.aemeasurable
  have hzK : ∀ᵐ x ∂mu, z x ∈ K := by
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact ⟨S.base_mem (Metric.ball_subset_closedBall hx), mem_univ _⟩
  have hAF : Measurable (K.indicator (fun z => S.flux z.1 z.2)) := by
    convert S.flux_continuous.measurable_piecewise (continuousOn_const (c := 0)) hK using 1
    funext z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz, piecewise_eq_of_mem _ _ _ hz]
    · rw [indicator_of_notMem hz, piecewise_eq_of_notMem _ _ _ hz]
  have hAB : Measurable (K.indicator (fun z => S.source z.1 z.2)) := by
    convert S.source_continuous.measurable_piecewise (continuousOn_const (c := 0)) hK using 1
    funext z
    by_cases hz : z ∈ K
    · rw [indicator_of_mem hz, piecewise_eq_of_mem _ _ _ hz]
    · rw [indicator_of_notMem hz, piecewise_eq_of_notMem _ _ _ hz]
  have hF : AEStronglyMeasurable (fun x => S.flux (x, u x) (q x)) mu := by
    apply (hAF.comp_aemeasurable hz).aestronglyMeasurable.congr
    filter_upwards [hzK] with x hx
    exact indicator_of_mem hx _
  have hB : AEStronglyMeasurable (fun x => S.source (x, u x) (q x)) mu := by
    apply (hAB.comp_aemeasurable hz).aestronglyMeasurable.congr
    filter_upwards [hzK] with x hx
    exact indicator_of_mem hx _
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hFlp : MemLp (fun x => S.constant * (1 + ‖q x‖)) 2 mu :=
    ((memLp_const (1 : ℝ)).add hq.norm).const_mul S.constant
  have hsq : MemLp (fun x => ‖q x‖ ^ 2) 1 mu := by
    simpa only [pow_two] using hq.norm.mul' hq.norm
  have hBlp : MemLp (fun x => S.constant * (1 + ‖q x‖ ^ 2)) 1 mu :=
    ((memLp_const (1 : ℝ)).add hsq).const_mul S.constant
  refine ⟨hFlp.mono' hF ?_, memLp_one_iff_integrable.mp (hBlp.mono' hB ?_)⟩
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact S.flux_bound _ (S.base_mem (Metric.ball_subset_closedBall hx)) _
  · filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact S.source_bound _ (S.base_mem (Metric.ball_subset_closedBall hx)) _

theorem component_memLp (S : SUQuadraticWeakSystem u V center R) :
    let mu := volume.restrict (Metric.ball center R)
    (∀ a i, MemLp (S.componentFlux a i) 2 mu) ∧
      ∀ a, Integrable (S.componentSource a) mu := by
  obtain ⟨hF, hB⟩ := S.operator_memLp
  refine ⟨fun a i => ?_, fun a => ?_⟩
  · exact (ContinuousLinearMap.apply ℝ ℝ (suColumnBasis a i)).comp_memLp' hF
  · exact (ContinuousLinearMap.apply ℝ ℝ (EuclideanSpace.single a (1 : ℝ))).integrable_comp hB

theorem scalar_equation (S : SUQuadraticWeakSystem u V center R) (a : Fin m)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center R) :
    (∫ x in Metric.ball center R, ∑ i : Fin 2,
      S.componentFlux a i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x in Metric.ball center R, S.componentSource a x * phi x := by
  let eta (x : LoopPlane) := phi x • EuclideanSpace.single a (1 : ℝ)
  have heta : ContDiff ℝ ∞ eta := hphi.smul contDiff_const
  have hD (x : LoopPlane) (i : Fin 2) :
      fderiv ℝ eta x (EuclideanSpace.single i 1) =
        fderiv ℝ phi x (EuclideanSpace.single i 1) • EuclideanSpace.single a (1 : ℝ) := by
    rw [((hphi.differentiable (by simp) x).hasFDerivAt.smul_const
      (EuclideanSpace.single a (1 : ℝ))).fderiv]
    rfl
  have hp (x : LoopPlane) :
      (fderiv ℝ eta x (EuclideanSpace.single 0 1),
        fderiv ℝ eta x (EuclideanSpace.single 1 1)) =
      fderiv ℝ phi x (EuclideanSpace.single 0 1) • suColumnBasis a 0 +
        fderiv ℝ phi x (EuclideanSpace.single 1 1) • suColumnBasis a 1 := by
    rw [hD, hD]
    simp [suColumnBasis]
  have heq := S.equation eta heta hc.smul_right
    ((tsupport_smul_subset_left _ _).trans hs)
  simpa only [hp, map_add, map_smul, smul_eq_mul, eta, componentFlux, componentSource,
    Fin.sum_univ_two, mul_comm] using heq

theorem indicator_equation (S : SUQuadraticWeakSystem u V center R)
    {r : ℝ} (hrR : r ≤ R) (a : Fin m)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center r) :
    (∫ x, ∑ i : Fin 2, (Metric.ball center r).indicator (S.componentFlux a i) x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      ∫ x, (Metric.ball center r).indicator (S.componentSource a) x * phi x := by
  classical
  have hsub := Metric.ball_subset_ball (x := center) hrR
  have heq := S.scalar_equation a hphi hc (hs.trans hsub)
  have hD (x : LoopPlane) (hx : x ∉ Metric.ball center r) (i : Fin 2) :
      fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
    image_eq_zero_of_notMem_tsupport
      (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
      (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
  have hp (x : LoopPlane) (hx : x ∉ Metric.ball center r) : phi x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hx (hs h))
  rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by simp only [hD x hx.2, mul_zero, Finset.sum_const_zero]),
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_ball hsub
      (fun x hx => by rw [hp x hx.2, mul_zero])] at heq
  have hleft : (fun x => ∑ i : Fin 2,
      (Metric.ball center r).indicator (S.componentFlux a i) x *
        fderiv ℝ phi x (EuclideanSpace.single i 1)) =
      (Metric.ball center r).indicator (fun x => ∑ i : Fin 2,
        S.componentFlux a i x * fderiv ℝ phi x (EuclideanSpace.single i 1)) := by
    funext x
    by_cases hx : x ∈ Metric.ball center r <;> simp [hx]
  have hright : (fun x => (Metric.ball center r).indicator (S.componentSource a) x * phi x) =
      (Metric.ball center r).indicator (fun x => S.componentSource a x * phi x) := by
    funext x
    by_cases hx : x ∈ Metric.ball center r <;> simp [hx]
  rw [hleft, hright, integral_indicator measurableSet_ball, integral_indicator measurableSet_ball]
  exact heq

end SUQuadraticWeakSystem

end PoincareConjecture.M60
