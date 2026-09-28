import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalPotential
import PoincareConjecture.Proofs.Horizon.Analysis.Elliptic.Regularity.Sobolev.Embedding.Subcritical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.InteriorEstimates
open Poincare.Analysis.Sobolev.EuclideanEmbedding.EuclideanSubcritical

noncomputable section

namespace PoincareConjecture.M60

theorem suNaturalGrowth_error_bound
    {I K J L a b c d e nu C : ℝ} (hnu : 0 < nu) (hC : 0 ≤ C)
    (hI : 0 ≤ I) (hK : 0 ≤ K) (hJ : 0 ≤ J)
    (hmain : nu * I ≤ L + a + b + c + d + e)
    (ha : a ^ 2 ≤ C ^ 2 * I * K)
    (hb : b ^ 2 ≤ 4 * C ^ 2 * I * J)
    (hc : c ^ 2 ≤ 4 * C ^ 2 * K * J)
    (hd : d ^ 2 ≤ C ^ 2 * I * K) (he : e ≤ 2 * C * K) :
    nu / 2 * I ≤ L + (8 * C ^ 2 / nu + 3 * C) * (K + J) := by
  have hfirst {z : ℝ} (hz : z ^ 2 ≤ C ^ 2 * I * K) :
      2 * z ≤ (nu / 4) * I + (4 * C ^ 2 / nu) * K := by
    apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
    apply hz.trans_eq
    field_simp
  have hsecond : 2 * b ≤ (nu / 4) * I + (16 * C ^ 2 / nu) * J := by
    apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
    apply hb.trans_eq
    field_simp
    ring
  have hthird : 2 * c ≤ (2 * C) * K + (2 * C) * J := by
    apply two_mul_le_add_of_sq_le_mul (by positivity) (by positivity)
    exact hc.trans_eq (by ring)
  have hposK : 0 ≤ (4 * C ^ 2 / nu) * K := by positivity
  have hposJ : 0 ≤ 2 * C * J := by positivity
  have hposI : 0 ≤ nu * I := by positivity
  simp only [div_eq_mul_inv] at hfirst hsecond hposK ⊢
  nlinarith [hfirst ha, hfirst hd, hsecond, hthird]

private theorem suDual_apply_sq_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (v : E) : (L v) ^ 2 ≤ ‖L‖ ^ 2 * ‖v‖ ^ 2 := by
  have h := pow_le_pow_left₀ (norm_nonneg (L v)) (L.le_opNorm v) 2
  simpa only [Real.norm_eq_abs, sq_abs, mul_pow] using h

theorem suNaturalGrowth_dual_pointwise
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (P A : E →L[ℝ] ℝ) (B D : F →L[ℝ] ℝ) (q j : E) (u : F)
    {xi W H nu C : ℝ} (hnu : 0 < nu) (hC : 0 ≤ C) (hW : 0 ≤ W) (hH : 0 ≤ H)
    (hmono : nu * W * ‖q‖ ^ 2 ≤ P q)
    (hP : ‖P‖ ≤ C * W * ‖q‖)
    (hA : ‖A‖ ^ 2 ≤ C ^ 2 * W * H * (1 + ‖u‖ ^ 2))
    (hB : ‖B‖ ^ 2 ≤ C ^ 2 * W * H * ‖q‖ ^ 2)
    (hD : ‖D‖ ≤ C * H * (1 + ‖u‖)) :
    nu / 2 * (W * xi ^ 2 * ‖q‖ ^ 2) ≤
      (P + A) (xi ^ 2 • q + (2 * xi) • j) - (B + D) (xi ^ 2 • u) +
      (8 * C ^ 2 / nu + 3 * C) *
        (H * xi ^ 2 * (1 + ‖u‖ ^ 2) + W * ‖j‖ ^ 2) := by
  let I := W * xi ^ 2 * ‖q‖ ^ 2
  let K := H * xi ^ 2 * (1 + ‖u‖ ^ 2)
  let J := W * ‖j‖ ^ 2
  let L := (P + A) (xi ^ 2 • q + (2 * xi) • j) - (B + D) (xi ^ 2 • u)
  have ha : (-xi ^ 2 * A q) ^ 2 ≤ C ^ 2 * I * K := by
    have h1 := mul_le_mul_of_nonneg_left (suDual_apply_sq_le A q) (sq_nonneg (xi ^ 2))
    have h2 := mul_le_mul_of_nonneg_right hA
      (by positivity : 0 ≤ xi ^ 4 * ‖q‖ ^ 2)
    dsimp only [I, K]
    nlinarith
  have hb : (-2 * xi * P j) ^ 2 ≤ 4 * C ^ 2 * I * J := by
    have hp := pow_le_pow_left₀ (norm_nonneg P) hP 2
    have h1 := mul_le_mul_of_nonneg_left (suDual_apply_sq_le P j)
      (by positivity : 0 ≤ 4 * xi ^ 2)
    have h2 := mul_le_mul_of_nonneg_right hp
      (by positivity : 0 ≤ 4 * xi ^ 2 * ‖j‖ ^ 2)
    dsimp only [I, J]
    nlinarith
  have hc : (-2 * xi * A j) ^ 2 ≤ 4 * C ^ 2 * K * J := by
    have h1 := mul_le_mul_of_nonneg_left (suDual_apply_sq_le A j)
      (by positivity : 0 ≤ 4 * xi ^ 2)
    have h2 := mul_le_mul_of_nonneg_right hA
      (by positivity : 0 ≤ 4 * xi ^ 2 * ‖j‖ ^ 2)
    dsimp only [K, J]
    nlinarith
  have hd : (xi ^ 2 * B u) ^ 2 ≤ C ^ 2 * I * K := by
    have h1 := mul_le_mul_of_nonneg_left (suDual_apply_sq_le B u) (sq_nonneg (xi ^ 2))
    have h2 := mul_le_mul_of_nonneg_right hB
      (by positivity : 0 ≤ xi ^ 4 * ‖u‖ ^ 2)
    have h3 : 0 ≤ C ^ 2 * W * H * ‖q‖ ^ 2 * xi ^ 4 := by positivity
    dsimp only [I, K]
    nlinarith
  have he : xi ^ 2 * D u ≤ 2 * C * K := by
    have h1 : D u ≤ ‖D‖ * ‖u‖ := (le_abs_self _).trans (D.le_opNorm u)
    have h2 := mul_le_mul_of_nonneg_right hD (norm_nonneg u)
    have h3 := mul_le_mul_of_nonneg_left
      (show (1 + ‖u‖) * ‖u‖ ≤ 2 * (1 + ‖u‖ ^ 2) by nlinarith [sq_nonneg (‖u‖ - 1)])
      (by positivity : 0 ≤ C * H)
    have h4 : D u ≤ C * H * (2 * (1 + ‖u‖ ^ 2)) := h1.trans (h2.trans (by nlinarith))
    have h := mul_le_mul_of_nonneg_left h4 (sq_nonneg xi)
    dsimp only [K]
    nlinarith
  apply suNaturalGrowth_error_bound hnu hC (by dsimp [I]; positivity)
    (by dsimp [K]; positivity) (by dsimp [J]; positivity) _ ha hb hc hd he
  have h := mul_le_mul_of_nonneg_left hmono (sq_nonneg xi)
  dsimp only [I, L]
  simp only [add_apply, map_add, map_smul, smul_eq_mul]
  nlinarith

theorem suWeakPartial_two_dim_memLp
    {center : LoopPlane} {r R : ℝ} (hrR : r < R)
    {u : LoopPlane → ℝ} {V : Fin 2 → LoopPlane → ℝ}
    (hu : MemLp u 2 (volume.restrict (Metric.ball center R)))
    (hV : ∀ i, MemLp (V i) 2 (volume.restrict (Metric.ball center R)))
    (hw : ∀ i, HasWeakPartialDeriv i (V i) u (Metric.ball center R))
    (q : ℝ) (hq : 1 ≤ q) :
    MemLp u (ENNReal.ofReal q) (volume.restrict (Metric.ball center r)) := by
  let O := Metric.ball center R
  let mu := volume.restrict O
  let : IsFiniteMeasure mu := ⟨by
    change volume.restrict (Metric.ball center R) univ < ⊤
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hsubset : Metric.ball center r ⊆ O := Metric.ball_subset_ball hrR.le
  by_cases hq2 : q ≤ 2
  · exact (hu.mono_exponent (by
      simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hq2)).mono_measure
        (Measure.restrict_mono hsubset le_rfl)
  have h2q : 2 < q := lt_of_not_ge hq2
  let p := 2 * q / (q + 2)
  have hden : 0 < q + 2 := by linarith
  have hp1 : 1 ≤ p := (le_div_iff₀ hden).mpr (by linarith)
  have hp2 : p < 2 := (div_lt_iff₀ hden).mpr (by linarith)
  have hpE : ENNReal.ofReal p ≤ 2 := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal hp2.le
  have hstar : 2 * p / (2 - p) = q := by
    dsimp only [p]
    field_simp
    ring
  obtain ⟨chi, hchi, hchic, _, hchi1, hchiO⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall center r) isOpen_ball
      (Metric.closedBall_subset_ball hrR)
  let v (x : LoopPlane) := chi x * u x
  let dv (i : Fin 2) (x : LoopPlane) :=
    chi x * V i x + fderiv ℝ chi x (EuclideanSpace.single i 1) * u x
  have hchiLp : MemLp chi ⊤ mu :=
    (hchi.continuous.memLp_of_hasCompactSupport hchic).restrict O
  have huP : MemLp u (ENNReal.ofReal p) mu := hu.mono_exponent hpE
  have hVLp : ∀ i, MemLp (V i) (ENNReal.ofReal p) mu :=
    fun i => (hV i).mono_exponent hpE
  have hv : MemLp v (ENNReal.ofReal p) mu := huP.mul' hchiLp
  have hdv (i : Fin 2) : MemLp (dv i) (ENNReal.ofReal p) mu := by
    have hdchi : MemLp (fun x => fderiv ℝ chi x (EuclideanSpace.single i 1)) ⊤ mu :=
      (((hchi.continuous_fderiv (by simp)).clm_apply continuous_const
        ).memLp_of_hasCompactSupport (hchic.fderiv_apply (𝕜 := ℝ) _)).restrict O
    exact ((hVLp i).mul' hchiLp).add (huP.mul' hdchi)
  have hwv (i : Fin 2) : HasWeakPartialDeriv i (dv i) v O :=
    (hw i).mul_smooth isOpen_ball hchi
      (hu.locallyIntegrable (by norm_num)) ((hV i).locallyIntegrable (by norm_num))
  have hvW : Euclidean.MemWkp 1 (ENNReal.ofReal p) v O :=
    Euclidean.MemWkp.one_iff_memW1p.mpr ⟨hv, fun i => ⟨dv i, hdv i, hwv i⟩⟩
  have hvq : MemLp v (ENNReal.ofReal q) mu := by
    refine ⟨hv.1, ?_⟩
    have hs := eLpNorm_p_star_le_const_mul_wkpNorm_of_memWkp hp1 hp2 isOpen_ball hvW
        hchic.mul_right (tsupport_mul_subset_left.trans hchiO)
    simp only [Nat.cast_ofNat, hstar] at hs
    exact hs.trans_lt (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (by norm_num))
      (Euclidean.wkpNorm_lt_top_of_memWkp hvW))
  apply (hvq.mono_measure (Measure.restrict_mono hsubset le_rfl)).ae_eq
  filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
  simp only [v, hchi1 x (Metric.ball_subset_closedBall hx), one_mul]

theorem suInitialGain_of_integral_diffQuot_bound
    {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)}
    {center : LoopPlane} {r outerRadius h0 : ℝ}
    (hr : 0 < r) (hro : r ≤ outerRadius) (hh0 : 0 < h0)
    (hu : ContinuousOn u (Metric.closedBall center r))
    (hu2 : MemLp u 2 (volume.restrict (Metric.ball center r)))
    (hV : ∀ i, MemLp (V i) 2 volume)
    (hw : ∀ (i : Fin 2) (a : Fin m),
      HasWeakPartialDeriv i (fun x => V i x a) (fun x => u x a) (Metric.ball center r))
    (C : Fin m → Fin 2 → ℝ)
    (hbound : ∀ (a : Fin m) (k : Fin 2) (h : ℝ), h ≠ 0 → |h| ≤ h0 →
      (∫ x in Metric.ball center r,
        ∑ i : Fin 2, diffQuot k h (fun y => V i y a) x ^ 2) ≤ C a k) :
    Nonempty (SUInitialGain u V center outerRadius) := by
  have hc : IsCompact (closure (Metric.ball center r)) := by
    rw [closure_ball _ hr.ne']
    exact isCompact_closedBall _ _
  choose H hHm hHw _hHn using fun (a : Fin m) (i k : Fin 2) =>
    exists_weakPartial_eLpNorm_le_of_integral_diffQuot_bound isOpen_ball hc
        (fun j => (hV j).eval_piLp a) hh0 (hbound a) i k
  have hsub : Metric.ball center (r / 2) ⊆ Metric.ball center r :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨{
    radius := r / 2
    radius_pos := half_pos hr
    radius_lt := (half_lt_self hr).trans_le hro
    coordinate_continuous := hu.mono (Metric.closedBall_subset_closedBall (by linarith))
    coordinate_memLp := hu2.mono_measure (Measure.restrict_mono hsub le_rfl)
    column_memLp := ?_
    weak_derivative := fun i a => (hw i a).restrict isOpen_ball hsub
    hessian := fun i k x => WithLp.toLp 2 (fun a => H a i k x)
    hessian_memLp := ?_
    second_weak_derivative := fun i k a => (hHw a i k).restrict isOpen_ball hsub
  }⟩
  · intro q hq i
    apply MemLp.of_eval_piLp
    intro a
    exact suWeakPartial_two_dim_memLp (half_lt_self hr)
      ((hV i).eval_piLp a |>.restrict _) (hHm a i) (hHw a i) q hq
  · intro i k
    apply MemLp.of_eval_piLp
    intro a
    exact (hHm a i k).mono_measure (Measure.restrict_mono hsub le_rfl)

theorem suNaturalGrowth_translated_potential
    {center : LoopPlane} {r R kappa : ℝ} {H W : LoopPlane → ℝ}
    (hH : Integrable H) (hW : Integrable W)
    (hpot : ∀ phi : LoopPlane → ℝ, ContDiff ℝ ∞ phi → HasCompactSupport phi →
      tsupport phi ⊆ Metric.ball center R →
      (∫ x, H x * phi x ^ 2) ≤ kappa *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2)
    (a : LoopPlane) (ha : r + ‖a‖ ≤ R)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center r) :
    (∫ x, (H x + H (x + a)) * phi x ^ 2) ≤ kappa *
      ∫ x, (W x + W (x + a)) *
        ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  let psi (x : LoopPlane) := phi (x - a)
  have hpsi : ContDiff ℝ ∞ psi := hphi.comp (contDiff_id.sub contDiff_const)
  have hpsic : HasCompactSupport psi := by
    have ht := hc.comp_homeomorph (Homeomorph.addRight (-a))
    change HasCompactSupport (fun x => phi (x + -a)) at ht
    simpa only [psi, sub_eq_add_neg] using ht
  have hpsis : tsupport psi ⊆ Metric.ball center R := by
    have ht : tsupport psi ⊆ (fun x => x - a) ⁻¹' tsupport phi :=
      tsupport_comp_subset_preimage phi (continuous_id.sub continuous_const)
    intro x hx
    have hd : dist (x - a) center < r := hs (ht hx)
    have hx : dist x center ≤ ‖a‖ + dist (x - a) center := by
      calc
        _ ≤ dist x (x - a) + dist (x - a) center := dist_triangle _ _ _
        _ = _ := by rw [dist_eq_norm]; congr 2; abel
    exact lt_of_le_of_lt hx (by linarith)
  have hDp (x : LoopPlane) : fderiv ℝ psi x = fderiv ℝ phi (x - a) := by
    have hd := (hphi.differentiable (by simp) (x - a)).hasFDerivAt.comp x
      ((hasFDerivAt_id x).sub_const a)
    simpa only [psi, Function.comp_def, id_eq, ContinuousLinearMap.comp_id] using hd.fderiv
  have hshiftH : (∫ x, H (x + a) * phi x ^ 2) = ∫ x, H x * psi x ^ 2 := by
    simpa only [psi, add_sub_cancel_right] using
      integral_add_right_eq_self (fun x => H x * psi x ^ 2) a
  have hshiftW : (∫ x, W (x + a) *
      ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ psi x (EuclideanSpace.single i 1)) ^ 2 := by
    simpa only [hDp, add_sub_cancel_right] using integral_add_right_eq_self
      (fun x => W x * ∑ i : Fin 2, (fderiv ℝ psi x (EuclideanSpace.single i 1)) ^ 2) a
  have hsq {A : LoopPlane → ℝ} (hA : Integrable A) :
      Integrable (fun x => A x * phi x ^ 2) := by
    have hsqc : HasCompactSupport (fun x => phi x ^ 2) := hc.of_isClosed_subset
      (isClosed_tsupport _) (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) phi)
    exact memLp_one_iff_integrable.mp
      (((hphi.continuous.pow 2).memLp_of_hasCompactSupport hsqc : MemLp _ ⊤ volume
        ).mul' (memLp_one_iff_integrable.mpr hA))
  have hgrad {A : LoopPlane → ℝ} (hA : Integrable A) : Integrable (fun x => A x *
      ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) := by
    simp_rw [Finset.mul_sum]
    apply integrable_finsetSum
    intro i _
    have hd : MemLp (fun x => fderiv ℝ phi x (EuclideanSpace.single i 1)) ⊤ volume :=
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const
        ).memLp_of_hasCompactSupport (hc.fderiv_apply (𝕜 := ℝ) _)
    have hs2 : MemLp (fun x => (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) ⊤ volume :=
      by simpa only [pow_two] using hd.mul' hd
    exact memLp_one_iff_integrable.mp (hs2.mul' (memLp_one_iff_integrable.mpr hA))
  have hHt : Integrable (fun x => H (x + a)) :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable hH
  have hWt : Integrable (fun x => W (x + a)) :=
    (measurePreserving_add_right volume a).integrable_comp_of_integrable hW
  simp_rw [add_mul]
  rw [integral_add (hsq hH) (hsq hHt), integral_add (hgrad hW) (hgrad hWt), mul_add,
    hshiftH, hshiftW]
  exact add_le_add (hpot phi hphi hc (hs.trans
    (Metric.ball_subset_ball (by linarith [norm_nonneg a])))) (hpot psi hpsi hpsic hpsis)

theorem suNaturalGrowth_column_pointwise {m : ℕ}
    (L : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) →L[ℝ] ℝ)
    (B : EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ)
    (d : Fin 2 → EuclideanSpace ℝ (Fin m)) (w : EuclideanSpace ℝ (Fin m))
    (dx : Fin 2 → ℝ) {xi H W nu C : ℝ}
    (hnu : 0 ≤ nu) (hC : 0 ≤ C) (hW : 0 ≤ W)
    (hbound : nu * (W * xi ^ 2 * ‖(d 0, d 1)‖ ^ 2) ≤
      L (xi ^ 2 • (d 0, d 1) + (2 * xi) • (dx 0 • w, dx 1 • w)) -
        B (xi ^ 2 • w) + C *
          (H * xi ^ 2 * (1 + ‖w‖ ^ 2) + W * ‖(dx 0 • w, dx 1 • w)‖ ^ 2)) :
    nu / 2 * (W * ∑ a : Fin m, ∑ i : Fin 2, (xi * d i a) ^ 2) ≤
      (∑ a : Fin m, ∑ i : Fin 2, L (suColumnBasis a i) *
        (xi ^ 2 * d i a + 2 * xi * dx i * w a)) -
      (∑ a : Fin m, B (EuclideanSpace.single a 1) * (xi ^ 2 * w a)) +
      C * ((H * xi ^ 2 + ∑ a : Fin m, H * (xi * w a) ^ 2) +
        W * ∑ a : Fin m, ∑ i : Fin 2, (dx i * w a) ^ 2) := by
  have hsum (v : Fin 2 → EuclideanSpace ℝ (Fin m)) :
      (∑ a : Fin m, ∑ i : Fin 2, v i a ^ 2) = ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 := by
    simp only [Fin.sum_univ_two, Finset.sum_add_distrib,
      ← EuclideanSpace.real_norm_sq_eq]
  have hnorm (v : Fin 2 → EuclideanSpace ℝ (Fin m)) :
      ‖(v 0, v 1)‖ ^ 2 ≤ ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ∧
      ‖v 0‖ ^ 2 + ‖v 1‖ ^ 2 ≤ 2 * ‖(v 0, v 1)‖ ^ 2 := by
    have h0 := pow_le_pow_left₀ (norm_nonneg (v 0))
      (le_max_left ‖v 0‖ ‖v 1‖) 2
    have h1 := pow_le_pow_left₀ (norm_nonneg (v 1))
      (le_max_right ‖v 0‖ ‖v 1‖) 2
    rw [Prod.norm_def]
    constructor
    · rcases le_total ‖v 0‖ ‖v 1‖ with h | h
      · rw [max_eq_right h]
        nlinarith [sq_nonneg ‖v 0‖]
      · rw [max_eq_left h]
        nlinarith [sq_nonneg ‖v 1‖]
    · linarith
  have hprincipal : (∑ a : Fin m, ∑ i : Fin 2, (xi * d i a) ^ 2) ≤
      2 * xi ^ 2 * ‖(d 0, d 1)‖ ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum]
    rw [hsum]
    nlinarith [mul_le_mul_of_nonneg_left (hnorm d).2 (sq_nonneg xi)]
  have hcutoff : ‖(dx 0 • w, dx 1 • w)‖ ^ 2 ≤
      ∑ a : Fin m, ∑ i : Fin 2, (dx i * w a) ^ 2 := by
    have h := (hnorm (fun i => dx i • w)).1
    rw [← hsum (fun i => dx i • w)] at h
    simpa only [PiLp.smul_apply, smul_eq_mul] using h
  have hpotential : H * xi ^ 2 * (1 + ‖w‖ ^ 2) =
      H * xi ^ 2 + ∑ a : Fin m, H * (xi * w a) ^ 2 := by
    simp only [mul_pow, ← Finset.mul_sum, ← EuclideanSpace.real_norm_sq_eq]
    ring
  have hL : L (xi ^ 2 • (d 0, d 1) + (2 * xi) • (dx 0 • w, dx 1 • w)) =
      ∑ a : Fin m, ∑ i : Fin 2, L (suColumnBasis a i) *
        (xi ^ 2 * d i a + 2 * xi * dx i * w a) := by
    have he := suColumnDual_pairing L (fun i => xi ^ 2 • d i + (2 * xi * dx i) • w)
    have hv : (xi ^ 2 • d 0 + (2 * xi * dx 0) • w,
        xi ^ 2 • d 1 + (2 * xi * dx 1) • w) =
        xi ^ 2 • (d 0, d 1) + (2 * xi) • (dx 0 • w, dx 1 • w) := by
      simp only [Prod.smul_mk, Prod.mk_add_mk, smul_smul]
    rw [hv] at he
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul] using he.symm
  have hB : B (xi ^ 2 • w) =
      ∑ a : Fin m, B (EuclideanSpace.single a 1) * (xi ^ 2 * w a) := by
    simpa only [PiLp.smul_apply, smul_eq_mul] using
      (suCoordinateDual_pairing B (xi ^ 2 • w)).symm
  rw [hpotential, hL, hB] at hbound
  have hp := mul_le_mul_of_nonneg_left hprincipal (mul_nonneg hnu hW)
  have hj := mul_le_mul_of_nonneg_left hcutoff (mul_nonneg hC hW)
  nlinarith

theorem suNaturalGrowth_cutoff_remainder_bounded
    {m : ℕ} {p r t : ℝ≥0∞} (hp : 1 ≤ p) (hpfin : p ≠ ⊤) [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p p t] [ENNReal.HolderConjugate r t]
    {u : Fin m → LoopPlane → ℝ} {du : Fin m → Fin 2 → LoopPlane → ℝ}
    {xi H W : LoopPlane → ℝ} {kappa : ℝ} (hkappa : 0 ≤ kappa)
    (hu : ∀ a, Continuous (u a)) (huc : ∀ a, HasCompactSupport (u a))
    (hdu : ∀ a i, MemLp (du a i) p volume)
    (hw : ∀ a i, HasWeakPartialDeriv i (du a i) (u a) univ)
    (hxi : ContDiff ℝ ∞ xi) (hxic : HasCompactSupport xi) (hxi1 : ∀ x, |xi x| ≤ 1)
    (hH : Integrable H) (hH0 : ∀ x, 0 ≤ H x) (hW : MemLp W r volume) :
    ∃ C : ℝ, ∀ (k : Fin 2) (h : ℝ),
      (∫ x, (H x + translate k h H x) * xi x ^ 2) + (1 + 2 * kappa) *
        (∫ x, (W x + translate k h W x) * ∑ a : Fin m, ∑ i : Fin 2,
          (fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot k h (u a) x) ^ 2) ≤ C := by
  choose C hC hbound using fun a : Fin m => suWeightedCutoff_diffQuot_bounded (t := t) hp hpfin
    (hu a) (huc a) (hdu a) (hw a) hxi hxic hW
  refine ⟨2 * (∫ x, H x) + (1 + 2 * kappa) * ∑ a : Fin m, ∑ i : Fin 2, C a i,
    fun k h => ?_⟩
  have hHt : Integrable (translate k h H) :=
    (measurePreserving_add_right volume (h • EuclideanSpace.single k (1 : ℝ))
      ).integrable_comp_of_integrable hH
  have hsum : Integrable (fun x => H x + translate k h H x) := hH.add hHt
  have hsqc : HasCompactSupport (fun x => xi x ^ 2) := hxic.of_isClosed_subset
    (isClosed_tsupport _) (tsupport_comp_subset (g := fun s : ℝ => s ^ 2) (by simp) xi)
  have hsq : MemLp (fun x => xi x ^ 2) ⊤ volume :=
    (show Continuous (fun x => xi x ^ 2) from hxi.continuous.pow 2
      ).memLp_of_hasCompactSupport hsqc
  have hKI : Integrable (fun x => (H x + translate k h H x) * xi x ^ 2) :=
    memLp_one_iff_integrable.mp (hsq.mul' (memLp_one_iff_integrable.mpr hsum))
  have hK : (∫ x, (H x + translate k h H x) * xi x ^ 2) ≤ 2 * ∫ x, H x := by
    have hmono := integral_mono hKI hsum (fun x =>
      mul_le_of_le_one_right (add_nonneg (hH0 x) (hH0 _))
        (by nlinarith [sq_abs (xi x), hxi1 x, abs_nonneg (xi x)]))
    rw [integral_add hH hHt] at hmono
    have hshift : (∫ x, translate k h H x) = ∫ x, H x :=
      integral_add_right_eq_self H (h • EuclideanSpace.single k (1 : ℝ))
    rw [hshift] at hmono
    linarith
  have hJ : (∫ x, (W x + translate k h W x) * ∑ a : Fin m, ∑ i : Fin 2,
      (fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot k h (u a) x) ^ 2) ≤
      ∑ a : Fin m, ∑ i : Fin 2, C a i := by
    simp_rw [Finset.mul_sum]
    rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _
      (fun i _ => (hbound a i k h).1))]
    apply Finset.sum_le_sum
    intro a _
    rw [integral_finsetSum _ (fun i _ => (hbound a i k h).1)]
    exact Finset.sum_le_sum fun i _ => (hbound a i k h).2
  exact add_le_add hK (mul_le_mul_of_nonneg_left hJ (by positivity))

namespace SUQuadraticWeakSystem

variable {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
  {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}

theorem flux_coercive (S : SUQuadraticWeakSystem u V center R)
    {x : LoopPlane × EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ Metric.closedBall center R ×ˢ
      Metric.closedBall (u center) S.targetRadius)
    (q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) :
    S.nu / 2 * (1 + ‖q‖ ^ 2) - (S.nu / 2 + S.constant ^ 2 / S.nu) ≤
      S.flux x q q := by
  have hmono := S.flux_monotone x hx q 0
  simp only [sub_zero, sub_apply] at hmono
  have h0 : ‖S.flux x 0‖ ≤ S.constant := by
    simpa only [norm_zero, add_zero, mul_one] using S.flux_bound x hx 0
  have hlow : -(S.constant * ‖q‖) ≤ S.flux x 0 q := by
    have h := (S.flux x 0).le_opNorm q
    have hb := mul_le_mul_of_nonneg_right h0 (norm_nonneg q)
    exact (neg_le_neg (h.trans hb)).trans (neg_abs_le _)
  have hy : 2 * (S.constant * ‖q‖) ≤
      S.nu * ‖q‖ ^ 2 + S.constant ^ 2 / S.nu := by
    apply two_mul_le_add_of_sq_le_mul (by positivity [S.nu_pos])
      (by positivity [S.nu_pos])
    field_simp [S.nu_pos.ne']
    exact le_rfl
  have hnonneg : 0 ≤ S.constant ^ 2 / S.nu := by positivity [S.nu_pos]
  nlinarith

theorem difference_pointwise (S : SUQuadraticWeakSystem u V center R)
    {x y : LoopPlane × EuclideanSpace ℝ (Fin m)}
    (hx : x ∈ Metric.closedBall center R ×ˢ
      Metric.closedBall (u center) S.targetRadius)
    (hy : y ∈ Metric.closedBall center R ×ˢ
      Metric.closedBall (u center) S.targetRadius)
    (q r j : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
    (w : EuclideanSpace ℝ (Fin m)) {h xi : ℝ} (hh : h ≠ 0)
    (hbase : ‖y - x‖ ≤ |h| * (1 + ‖w‖)) :
    let d := h⁻¹ • (q - r)
    let H := 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2
    S.nu / 2 * (xi ^ 2 * ‖d‖ ^ 2) ≤
      (h⁻¹ • (S.flux y q - S.flux x r)) (xi ^ 2 • d + (2 * xi) • j) -
      (h⁻¹ • (S.source y q - S.source x r)) (xi ^ 2 • w) +
      (32 * S.constant ^ 2 / S.nu + 6 * S.constant) *
        (H * xi ^ 2 * (1 + ‖w‖ ^ 2) + ‖j‖ ^ 2) := by
  let d := h⁻¹ • (q - r)
  let H := 2 + ‖q‖ ^ 2 + ‖r‖ ^ 2
  let P := h⁻¹ • (S.flux y q - S.flux y r)
  let A := h⁻¹ • (S.flux y r - S.flux x r)
  let B := h⁻¹ • (S.source y q - S.source y r)
  let D := h⁻¹ • (S.source y r - S.source x r)
  have hnu := S.nu_pos
  have hC := S.constant_pos
  have hcancel : |h⁻¹| * |h| = 1 := by simp [abs_inv, hh]
  have hd : ‖d‖ = |h⁻¹| * ‖q - r‖ := by simp [d, norm_smul]
  have hmono : S.nu * ‖d‖ ^ 2 ≤ P d := by
    have hm := mul_le_mul_of_nonneg_left (S.flux_monotone y hy q r) (sq_nonneg h⁻¹)
    simpa only [d, P, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
      smul_apply, map_smul, smul_eq_mul] using
      (show S.nu * (h⁻¹ ^ 2 * ‖q - r‖ ^ 2) ≤
        h⁻¹ * (h⁻¹ * (S.flux y q - S.flux y r) (q - r)) by nlinarith)
  have hP : ‖P‖ ≤ S.constant * ‖d‖ := by
    calc
      ‖P‖ = |h⁻¹| * ‖S.flux y q - S.flux y r‖ := by simp [P, norm_smul]
      _ ≤ |h⁻¹| * (S.constant * ‖q - r‖) :=
        mul_le_mul_of_nonneg_left (S.flux_gradient_bound y hy q r) (abs_nonneg _)
      _ = _ := by rw [hd]; ring
  have hA : ‖A‖ ≤ S.constant * (1 + ‖r‖) * (1 + ‖w‖) := by
    calc
      ‖A‖ = |h⁻¹| * ‖S.flux y r - S.flux x r‖ := by simp [A, norm_smul]
      _ ≤ |h⁻¹| * (S.constant * (1 + ‖r‖) * ‖y - x‖) :=
        mul_le_mul_of_nonneg_left (S.flux_base_bound x hx y hy r) (abs_nonneg _)
      _ ≤ |h⁻¹| * (S.constant * (1 + ‖r‖) * (|h| * (1 + ‖w‖))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbase (by positivity))
          (abs_nonneg _)
      _ = _ := by
        calc
          _ = (|h⁻¹| * |h|) * (S.constant * (1 + ‖r‖) * (1 + ‖w‖)) := by ring
          _ = _ := by rw [hcancel, one_mul]
  have hB : ‖B‖ ≤ S.constant * (1 + ‖q‖ + ‖r‖) * ‖d‖ := by
    calc
      ‖B‖ = |h⁻¹| * ‖S.source y q - S.source y r‖ := by simp [B, norm_smul]
      _ ≤ |h⁻¹| * (S.constant * (1 + ‖q‖ + ‖r‖) * ‖q - r‖) :=
        mul_le_mul_of_nonneg_left (S.source_gradient_bound y hy q r) (abs_nonneg _)
      _ = _ := by rw [hd]; ring
  have hD : ‖D‖ ≤ S.constant * H * (1 + ‖w‖) := by
    have hb := S.source_base_bound x hx y hy r
    have ht := mul_le_mul_of_nonneg_left
      (hb.trans (mul_le_mul_of_nonneg_left hbase (by positivity))) (abs_nonneg h⁻¹)
    have he : |h⁻¹| * (S.constant * (1 + ‖r‖ ^ 2) * (|h| * (1 + ‖w‖))) =
        S.constant * (1 + ‖r‖ ^ 2) * (1 + ‖w‖) := by
      calc
        _ = (|h⁻¹| * |h|) * (S.constant * (1 + ‖r‖ ^ 2) * (1 + ‖w‖)) := by ring
        _ = _ := by rw [hcancel, one_mul]
    rw [he] at ht
    rw [show ‖D‖ = |h⁻¹| * ‖S.source y r - S.source x r‖ by simp [D, norm_smul]]
    exact ht.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (by dsimp [H]; nlinarith [sq_nonneg ‖q‖]) hC.le)
      (by positivity))
  have hAsq : ‖A‖ ^ 2 ≤ (2 * S.constant) ^ 2 * H * (1 + ‖w‖ ^ 2) := by
    have ha := pow_le_pow_left₀ (norm_nonneg A) hA 2
    have hr : (1 + ‖r‖) ^ 2 ≤ 2 * H := by
      dsimp [H]
      nlinarith [sq_nonneg (‖r‖ - 1), sq_nonneg ‖q‖]
    have hw : (1 + ‖w‖) ^ 2 ≤ 2 * (1 + ‖w‖ ^ 2) := by
      nlinarith [sq_nonneg (‖w‖ - 1)]
    have hp := mul_le_mul hr hw (sq_nonneg _) (by dsimp [H]; positivity)
    have hb := mul_le_mul_of_nonneg_left hp (sq_nonneg S.constant)
    nlinarith
  have hBsq : ‖B‖ ^ 2 ≤ (2 * S.constant) ^ 2 * H * ‖d‖ ^ 2 := by
    have hb := pow_le_pow_left₀ (norm_nonneg B) hB 2
    have hp : (1 + ‖q‖ + ‖r‖) ^ 2 ≤ 4 * H := by
      dsimp [H]
      nlinarith [sq_nonneg (‖q‖ - ‖r‖), sq_nonneg (‖q‖ - 1),
        sq_nonneg (‖r‖ - 1)]
    have hm := mul_le_mul_of_nonneg_left hp (by positivity : 0 ≤ S.constant ^ 2 * ‖d‖ ^ 2)
    nlinarith
  have hmain := suNaturalGrowth_dual_pointwise P A B D d j w
    (xi := xi) (W := 1) (H := H) hnu (show 0 ≤ 2 * S.constant by positivity)
    zero_le_one (by dsimp [H]; positivity)
    (by simpa only [mul_one] using hmono)
    (by simp only [mul_one]; nlinarith [norm_nonneg d])
    (by simpa only [mul_one] using hAsq)
    (by simpa only [mul_one] using hBsq)
    (hD.trans (by
      have hpos : 0 ≤ S.constant * H * (1 + ‖w‖) := by dsimp [H]; positivity
      nlinarith))
  have hPA : P + A = h⁻¹ • (S.flux y q - S.flux x r) := by
    dsimp [P, A]
    rw [← smul_add]
    congr 1
    abel
  have hBD : B + D = h⁻¹ • (S.source y q - S.source x r) := by
    dsimp [B, D]
    rw [← smul_add]
    congr 1
    abel
  rw [hPA, hBD] at hmain
  convert hmain using 1 <;> ring

end SUQuadraticWeakSystem

end PoincareConjecture.M60
