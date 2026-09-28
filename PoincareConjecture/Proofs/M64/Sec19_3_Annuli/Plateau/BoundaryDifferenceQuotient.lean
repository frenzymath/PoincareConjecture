import PoincareConjecture.Proofs.M64.Sec19_3_Annuli.Plateau.BoundaryNaturalGrowthTest

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Sobolev.DifferenceQuotient
open Poincare.Analysis.Sobolev.Euclidean Poincare.Analysis.Sobolev.NirenbergStandardTest

namespace PoincareConjecture

theorem m64DiffQuot_integral_pairing
    {p q : ℝ≥0∞} [ENNReal.HolderConjugate q p]
    {f v : LoopPlane → ℝ} (hf : MemLp f q volume) (hv : MemLp v p volume)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0) :
    (∫ x, diffQuot k h f x * v x) = -(∫ x, f x * diffQuot k (-h) v x) := by
  have hfv := memLp_one_iff_integrable.mp (hv.mul' hf)
  have htv := memLp_one_iff_integrable.mp (hv.mul' (memLp_translate k h hf))
  have hft := memLp_one_iff_integrable.mp ((memLp_translate k (-h) hv).mul' hf)
  have ht : (∫ x, translate k h f x * v x) = ∫ x, f x * translate k (-h) v x := by
    have he := integral_add_right_eq_self (μ := (volume : Measure LoopPlane))
      (fun x : LoopPlane => f (x + h • EuclideanSpace.single k 1) * v x)
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

theorem m64DiffQuot_tangent_zero_below
    {u : LoopPlane → ℝ} (hu : ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (h : ℝ) : ∀ p : LoopPlane, p 1 < 0 → diffQuot 0 h u p = 0 := by
  intro p hp
  by_cases hh : h = 0
  · simp only [hh, diffQuot_zero_h, Pi.zero_apply]
  · rw [diffQuot_apply_of_ne 0 hh, hu p hp, hu _ (by simpa using hp)]
    simp

set_option maxHeartbeats 800000 in

theorem m64NaturalGrowth_boundary_nirenberg_identity
    {O : Set LoopPlane} (hO : IsOpen O)
    {F du : Fin 2 → LoopPlane → ℝ} {b u xi : LoopPlane → ℝ}
    (hF : ∀ i, MemLp (F i) 2 volume) (hb : Integrable b)
    (hu : Continuous u) (hdu : ∀ i, MemLp (du i) 2 volume)
    (hweak : ∀ i, HasWeakPartialDeriv i (du i) u univ)
    (hzero : ∀ p : LoopPlane, p 1 < 0 → u p = 0)
    (hxi : ContDiff ℝ ∞ xi) (hxic : HasCompactSupport xi)
    (heq : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ O ∩ {p : LoopPlane | 0 < p 1} →
      (∫ p, ∑ i : Fin 2, F i p * fderiv ℝ phi p (EuclideanSpace.single i 1)) =
        ∫ p, b p * phi p)
    {h : ℝ} (hh : h ≠ 0) (hsupp : cthickening |h| (tsupport xi) ⊆ O) :
    (∫ p, ∑ i : Fin 2, diffQuot 0 h (F i) p *
      (xi p ^ 2 * diffQuot 0 h (du i) p + 2 * xi p *
        fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h u p)) =
      ∫ p, diffQuot 0 h b p * (xi p ^ 2 * diffQuot 0 h u p) := by
  let w : LoopPlane → ℝ := fun p => xi p ^ 2 * diffQuot 0 h u p
  let dw := fun (i : Fin 2) (p : LoopPlane) => xi p ^ 2 * diffQuot 0 h (du i) p +
    2 * xi p * fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h u p
  have huc := continuous_diffQuot_of_continuous 0 h hu
  have hxi2c : HasCompactSupport (fun p => xi p ^ 2) :=
    hxic.of_isClosed_subset (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) xi)
  have hwc : HasCompactSupport w := hxi2c.mul_right
  have hwcont : Continuous w := (hxi.continuous.pow 2).mul huc
  have hdw (i : Fin 2) : MemLp (dw i) 2 volume := by
    apply ((M60.suWeakMap_diffQuot_memLp (hdu i) 0 h).mul'
      ((hxi.continuous.pow 2).memLp_of_hasCompactSupport hxi2c : MemLp _ ⊤ volume)).add
    have hc : Continuous (fun p => 2 * xi p *
        fderiv ℝ xi p (EuclideanSpace.single i 1) * diffQuot 0 h u p) :=
      ((continuous_const.mul hxi.continuous).mul
        ((hxi.continuous_fderiv (by simp)).clm_apply continuous_const)).mul huc
    exact hc.memLp_of_hasCompactSupport ((hxic.mul_left.mul_right).mul_right)
  have hvc := standardNirenbergTest_hasCompactSupport 0 h hxic u
  have hvcont : Continuous (standardNirenbergTest 0 h xi u) :=
    continuous_diffQuot_of_continuous 0 (-h) hwcont
  have hvO : tsupport (standardNirenbergTest 0 h xi u) ⊆ O := by
    intro p hp
    apply hsupp
    rcases standardNirenbergTest_tsupport_subset 0 h u hp with hp | hp
    · exact self_subset_cthickening _ hp
    · apply mem_cthickening_of_dist_le _ (p + (-h) • EuclideanSpace.single (0 : Fin 2) 1)
        _ _ hp
      simp [dist_eq_norm, norm_smul, Real.norm_eq_abs]
  have hwzero : ∀ p : LoopPlane, p 1 < 0 → w p = 0 := by
    intro p hp
    simp only [w, m64DiffQuot_tangent_zero_below hzero h p hp, mul_zero]
  have hvzero : ∀ p : LoopPlane, p 1 < 0 → standardNirenbergTest 0 h xi u p = 0 :=
    m64DiffQuot_tangent_zero_below hwzero (-h)
  have ht := m64NaturalGrowth_zero_boundary_test hO hF hb hvcont hvc hvO
    (hvcont.memLp_of_hasCompactSupport hvc)
    (fun i => M60.suWeakMap_diffQuot_memLp (hdw i) 0 (-h))
    (fun i => hasWeakPartialDeriv_standardNirenbergTest 0 i h hxi
      (by simpa using hu.locallyIntegrable)
      (by simpa using (hdu i).locallyIntegrable (by norm_num)) (hweak i)) hvzero heq
  have hpair (i : Fin 2) := m64DiffQuot_integral_pairing (hF i) (hdw i) 0 hh
  have hbpair := m64DiffQuot_integral_pairing (memLp_one_iff_integrable.mpr hb)
    (hwcont.memLp_of_hasCompactSupport hwc : MemLp w ⊤ volume) 0 hh
  have hIR (i : Fin 2) : Integrable (fun p => F i p * diffQuot 0 (-h) (dw i) p) := by
    simpa only [Pi.mul_apply] using!
      (hF i).integrable_mul (M60.suWeakMap_diffQuot_memLp (hdw i) 0 (-h))
  have hIL (i : Fin 2) : Integrable (fun p => diffQuot 0 h (F i) p * dw i p) := by
    simpa only [Pi.mul_apply] using!
      (M60.suWeakMap_diffQuot_memLp (hF i) 0 h).integrable_mul (hdw i)
  rw [integral_finsetSum _ (fun i _ => hIR i)] at ht
  rw [integral_finsetSum _ (fun i _ => hIL i)]
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpair i)
  rw [Finset.sum_neg_distrib, ht] at hsum
  exact hsum.trans hbpair.symm

end PoincareConjecture
