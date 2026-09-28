import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalGrowth









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Topology ContDiff ENNReal Manifold
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60



theorem suSmoothCutoff_poincare
    {center : LoopPlane} {R : ℝ} (hR : 0 < R) {phi : LoopPlane → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center R) :
    (∫ x, phi x ^ 2) ≤ 4 * R ^ 2 *
      ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  let X (x : LoopPlane) := x 0 - center 0
  let L : LoopPlane →L[ℝ] ℝ := EuclideanSpace.proj 0
  let D (i : Fin 2) (x : LoopPlane) := fderiv ℝ phi x (EuclideanSpace.single i 1)
  let J (x : LoopPlane) := ∑ i : Fin 2, D i x ^ 2
  have hX : ContDiff ℝ ∞ X := by
    exact L.contDiff.sub contDiff_const
  have hDX (x : LoopPlane) : fderiv ℝ X x (EuclideanSpace.single 0 1) = 1 := by
    have hd : HasFDerivAt X L x := L.hasFDerivAt.sub_const (center 0)
    rw [hd.fderiv]
    change (EuclideanSpace.single (0 : Fin 2) (1 : ℝ)) 0 = 1
    simp
  have hD2 (x : LoopPlane) :
      fderiv ℝ (fun y => phi y ^ 2) x (EuclideanSpace.single 0 1) = 2 * phi x * D 0 x := by
    rw [((hphi.differentiable (by simp) x).hasFDerivAt.pow 2).fderiv]
    simp [D, smul_apply]
  have hc2 : HasCompactSupport (fun x => phi x ^ 2) := hc.of_isClosed_subset
    (isClosed_tsupport _) (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) phi)
  have hDI (i : Fin 2) : Integrable (fun x => D i x ^ 2) := by
    have hd : Continuous (D i) := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const : Continuous (fun _ : LoopPlane => EuclideanSpace.single i (1 : ℝ)))
    have hdc : HasCompactSupport (D i) := hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
    have hsq : Continuous (fun x => D i x ^ 2) := hd.pow 2
    have hsqc : HasCompactSupport (fun x => D i x ^ 2) :=
      hdc.of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) (D i))
    exact hsq.integrable_of_hasCompactSupport hsqc
  have hJI : Integrable J := integrable_finsetSum _ fun i _ => hDI i
  have hI : Integrable (fun x => phi x ^ 2) :=
    (hphi.continuous.pow 2).integrable_of_hasCompactSupport hc2
  have hcross : Integrable (fun x => X x * (2 * phi x * D 0 x)) :=
    ((hX.continuous.mul ((continuous_const.mul hphi.continuous).mul
      ((hphi.continuous_fderiv (by simp)).clm_apply continuous_const))
      )).integrable_of_hasCompactSupport ((hc.mul_left.mul_right).mul_left)
  have hparts : (∫ x, X x * (2 * phi x * D 0 x)) = -(∫ x, phi x ^ 2) := by
    have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
      (f := X) (g := fun x => phi x ^ 2) (v := EuclideanSpace.single 0 1)
      (by simpa only [hDX, one_mul] using hI)
      (by simpa only [hD2] using hcross)
      ((hX.continuous.mul (hphi.continuous.pow 2)).integrable_of_hasCompactSupport hc2.mul_left)
      (fun x _ => hX.differentiable (by simp) x)
      (fun x _ => (hphi.pow 2).differentiable (by simp) x)
    simpa only [hDX, hD2, one_mul] using h
  have hpoint (x : LoopPlane) :
      -(X x * (2 * phi x * D 0 x)) ≤ (1 / 2 : ℝ) * phi x ^ 2 + 2 * R ^ 2 * J x := by
    have hj0 : 0 ≤ J x := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hj : D 0 x ^ 2 ≤ J x :=
      Finset.single_le_sum (fun i _ => sq_nonneg (D i x)) (Finset.mem_univ 0)
    by_cases hp : phi x = 0
    · simp only [hp, mul_zero, zero_mul, neg_zero, zero_pow (by decide : 2 ≠ 0), zero_add]
      positivity
    have hx : x ∈ Metric.ball center R := hs (subset_tsupport phi hp)
    have hdist : ‖x - center‖ < R := by simpa only [Metric.mem_ball, dist_eq_norm] using hx
    have hcoord : |X x| ≤ ‖x - center‖ := by
      change |(x - center) 0| ≤ ‖x - center‖
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le (x - center) (0 : Fin 2)
    have hX2 : X x ^ 2 ≤ R ^ 2 := by nlinarith [sq_abs (X x), abs_nonneg (X x)]
    have hbound : (-(X x * phi x * D 0 x)) ^ 2 ≤
        ((1 / 2 : ℝ) * phi x ^ 2) * (2 * R ^ 2 * J x) := by
      have ha := mul_le_mul_of_nonneg_left hX2
        (by positivity : 0 ≤ phi x ^ 2 * D 0 x ^ 2)
      have hb := mul_le_mul_of_nonneg_left hj (by positivity : 0 ≤ R ^ 2 * phi x ^ 2)
      nlinarith
    have hy := two_mul_le_add_of_sq_le_mul (by positivity : 0 ≤ (1 / 2 : ℝ) * phi x ^ 2)
      (by positivity : 0 ≤ 2 * R ^ 2 * J x) hbound
    nlinarith
  have hbound := integral_mono hcross.neg
    ((hI.const_mul (1 / 2 : ℝ)).add (hJI.const_mul (2 * R ^ 2))) hpoint
  simp only [Pi.neg_apply, Pi.add_apply] at hbound
  rw [integral_neg, hparts, neg_neg, integral_add (hI.const_mul (1 / 2 : ℝ))
    (hJI.const_mul (2 * R ^ 2)), integral_const_mul, integral_const_mul] at hbound
  change (∫ x, phi x ^ 2) ≤ 4 * R ^ 2 * ∫ x, J x
  linarith



theorem suWeightedCutoff_poincare
    {center : LoopPlane} {R : ℝ} (hR : 0 < R) {phi W : LoopPlane → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center R)
    (hW : ∀ x ∈ tsupport phi, 1 ≤ W x)
    (hI : Integrable (fun x => W x *
      ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2)) :
    (∫ x, phi x ^ 2) ≤ 4 * R ^ 2 *
      ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  let D (i : Fin 2) (x : LoopPlane) := fderiv ℝ phi x (EuclideanSpace.single i 1)
  have hd (i : Fin 2) : Continuous (D i) :=
    (hphi.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdc (i : Fin 2) : HasCompactSupport (D i) :=
    hc.fderiv_apply (𝕜 := ℝ) (EuclideanSpace.single i 1)
  have hdi (i : Fin 2) : Integrable (fun x => D i x ^ 2) := by
    have hsq : Continuous (fun x => D i x ^ 2) := (hd i).pow 2
    exact hsq.integrable_of_hasCompactSupport ((hdc i).of_isClosed_subset
      (isClosed_tsupport _)
      (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) (D i)))
  apply (suSmoothCutoff_poincare hR hphi hc hs).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply integral_mono (integrable_finsetSum _ fun i _ => hdi i) hI
  intro x
  change (∑ i : Fin 2, D i x ^ 2) ≤ W x * ∑ i : Fin 2, D i x ^ 2
  by_cases hx : x ∈ tsupport phi
  · exact le_mul_of_one_le_left (Finset.sum_nonneg fun i _ => sq_nonneg _) (hW x hx)
  · have hzero (i : Fin 2) : D i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun h => hx (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h))
    simp only [hzero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      Finset.sum_const_zero, mul_zero, le_refl]



theorem suNaturalGrowth_local_potential
    {center : LoopPlane} {R nu C0 A : ℝ} (hR : 0 < R) (hnu : 0 < nu)
    (hC0 : 0 ≤ C0) {phi H W : LoopPlane → ℝ}
    (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center R)
    (hW : ∀ x ∈ tsupport phi, 1 ≤ W x)
    (hI : Integrable (fun x => W x *
      ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2))
    (hpotential : nu / 2 * (∫ x, H x * phi x ^ 2) ≤ C0 * (∫ x, phi x ^ 2) +
      A * ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) :
    (∫ x, H x * phi x ^ 2) ≤ ((8 * C0 * R ^ 2 + 2 * A) / nu) *
      ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  have h := mul_le_mul_of_nonneg_left
    (suWeightedCutoff_poincare hR hphi hc hs hW hI) hC0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hnu).mpr
  nlinarith

set_option maxHeartbeats 600000 in



theorem suAlphaCoordinate_natural_value_bounds
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (b : M) {alpha : ℝ} (ha : 1 ≤ alpha)
    (center : LoopPlane) {R : ℝ} (hR : 0 ≤ R)
    (u0 : EuclideanSpace ℝ (Fin n)) (radius : ℝ)
    (hrange : closedBall u0 radius ⊆ (extChartAt (𝓡 n) b).target) :
    ∃ nu C C0 : ℝ, 0 < nu ∧ 0 < C ∧ 0 ≤ C0 ∧
      ∀ x ∈ closedBall center R ×ˢ closedBall u0 radius,
      ∀ q : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        let H := (1 + ‖q‖ ^ 2) ^ alpha
        let W := (1 + ‖q‖ ^ 2) ^ (alpha - 1)
        nu * H - C0 ≤ suAlphaCoordinateFlux g b alpha x q q ∧
          ‖suAlphaCoordinateFlux g b alpha x q‖ ^ 2 ≤ C ^ 2 * H * W ∧
          ‖suAlphaCoordinateSource g b alpha x q‖ ≤ C * H := by
  obtain ⟨nu, C, hnu, hC, hb⟩ := suAlphaCoordinate_natural_bounds g b ha center hR u0 radius hrange
  refine ⟨nu / 2, 2 * C, nu * (2 : ℝ) ^ alpha, by positivity, by positivity,
    by positivity, fun x hx q => ?_⟩
  let Q := 1 + ‖q‖ ^ 2
  let W := Q ^ (alpha - 1)
  let H := Q ^ alpha
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hQ1 : 1 ≤ Q := by dsimp [Q]; nlinarith [sq_nonneg ‖q‖]
  have hW : 1 ≤ W := Real.one_le_rpow hQ1 (by linarith)
  have hW0 : 0 ≤ W := zero_le_one.trans hW
  have hH0 : 0 ≤ H := Real.rpow_nonneg hQ.le _
  have hpower : H = W * Q := by
    dsimp only [H, W]
    calc
      Q ^ alpha = Q ^ (alpha - 1 + 1) := by congr 1; ring
      _ = Q ^ (alpha - 1) * Q ^ (1 : ℝ) := Real.rpow_add hQ _ _
      _ = _ := by rw [Real.rpow_one]
  have hF0 : suAlphaCoordinateFlux g b alpha x 0 = 0 := by
    apply ContinuousLinearMap.ext
    intro w
    simp [suAlphaCoordinateFlux, suAlphaFlux]
  have hS0 : suAlphaCoordinateSource g b alpha x 0 = 0 := by
    ext w
    simp [suAlphaCoordinateSource, suAlphaSource]
  have hmono : nu * (W + 1) * ‖q‖ ^ 2 ≤ suAlphaCoordinateFlux g b alpha x q q := by
    simpa only [hF0, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.one_rpow] using (hb x hx).1 q 0
  have hF : ‖suAlphaCoordinateFlux g b alpha x q‖ ≤ C * (W + 1) * ‖q‖ := by
    simpa only [hF0, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.one_rpow] using (hb x hx).2.1 q 0
  have hFn : ‖suAlphaCoordinateFlux g b alpha x q‖ ≤ 2 * C * W * ‖q‖ :=
    hF.trans (by
      nlinarith [mul_nonneg (mul_nonneg hC.le (norm_nonneg q)) (sub_nonneg.mpr hW)])
  have hS : ‖suAlphaCoordinateSource g b alpha x q‖ ≤
      C * (Q ^ (alpha - 1 / 2) + 1) * ‖q‖ := by
    simpa only [hS0, sub_zero, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero,
      Real.one_rpow] using (hb x hx).2.2.1 q 0
  refine ⟨?_, ?_, ?_⟩
  · have hnonneg : 0 ≤ suAlphaCoordinateFlux g b alpha x q q :=
      (show 0 ≤ nu * (W + 1) * ‖q‖ ^ 2 by positivity).trans hmono
    by_cases hq : ‖q‖ ^ 2 ≤ 1
    · have hH : H ≤ (2 : ℝ) ^ alpha := Real.rpow_le_rpow hQ.le
        (by dsimp [Q]; linarith) (by linarith)
      have hm := mul_le_mul_of_nonneg_left hH hnu.le
      change nu / 2 * H - nu * (2 : ℝ) ^ alpha ≤ _
      nlinarith [mul_nonneg hnu.le hH0]
    · have hq' : Q ≤ 2 * ‖q‖ ^ 2 := by dsimp [Q]; linarith
      have ht : H ≤ 2 * W * ‖q‖ ^ 2 := by
        rw [hpower]
        exact (mul_le_mul_of_nonneg_left hq' hW0).trans_eq (by ring)
      have hm := mul_le_mul_of_nonneg_left ht hnu.le
      have hpow : 0 ≤ nu * (2 : ℝ) ^ alpha := by positivity
      change nu / 2 * H - nu * (2 : ℝ) ^ alpha ≤ _
      nlinarith [show 0 ≤ nu * ‖q‖ ^ 2 by positivity]
  · have hs := pow_le_pow_left₀ (norm_nonneg _) hFn 2
    have hweight : W ^ 2 * ‖q‖ ^ 2 ≤ H * W := by
      rw [hpower]
      dsimp only [Q]
      nlinarith [sq_nonneg W]
    have hm := mul_le_mul_of_nonneg_left hweight (sq_nonneg (2 * C))
    change _ ≤ (2 * C) ^ 2 * H * W
    nlinarith
  · have hp : 1 ≤ Q ^ (alpha - 1 / 2) := Real.one_le_rpow hQ1 (by linarith)
    have hsqrt : ‖q‖ ≤ Real.sqrt Q := by
      have hs := Real.sq_sqrt hQ.le
      have hz := Real.sqrt_nonneg Q
      dsimp only [Q] at hs
      nlinarith [norm_nonneg q]
    have he : Q ^ (alpha - 1 / 2) * Real.sqrt Q = H := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hQ]
      congr 1
      ring
    have hm := mul_le_mul_of_nonneg_left hsqrt (Real.rpow_nonneg hQ.le (alpha - 1 / 2))
    rw [he] at hm
    have hS' := hS.trans (show C * (Q ^ (alpha - 1 / 2) + 1) * ‖q‖ ≤
        2 * C * (Q ^ (alpha - 1 / 2) * ‖q‖) by
      nlinarith [mul_nonneg (mul_nonneg hC.le (norm_nonneg q)) (sub_nonneg.mpr hp)])
    exact hS'.trans (mul_le_mul_of_nonneg_left hm (by positivity))

set_option maxHeartbeats 1200000 in

private theorem alpha_potential_bound
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    {r nu C C0 delta : ℝ} (hrR : r < R) (hnu : 0 < nu) (hC : 0 ≤ C) (hC0 : 0 ≤ C0)
    (_hdelta : 0 ≤ delta) (hsmall : C * delta ≤ nu / 4)
    (hosc : ∀ x ∈ ball center r, ‖u x - u center‖ ≤ delta)
    (hcoeff : ∀ x ∈ ball center r,
      let q := (V 0 x, V 1 x)
      let H := (1 + ‖q‖ ^ 2) ^ alpha
      let W := (1 + ‖q‖ ^ 2) ^ (alpha - 1)
      nu * H - C0 ≤ suAlphaCoordinateFlux g b alpha (x, u x) q q ∧
        ‖suAlphaCoordinateFlux g b alpha (x, u x) q‖ ^ 2 ≤ C ^ 2 * H * W ∧
        ‖suAlphaCoordinateSource g b alpha (x, u x) q‖ ≤ C * H)
    {phi : LoopPlane → ℝ} (hp : ContDiff ℝ ∞ phi) (hpc : HasCompactSupport phi)
    (hps : tsupport phi ⊆ ball center r) :
    let H := (ball center r).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha)
    let W := (ball center r).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1))
    Integrable (fun x => W x * ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) ∧
      nu / 2 * (∫ x, H x * phi x ^ 2) ≤ C0 * (∫ x, phi x ^ 2) +
        (4 * C ^ 2 * delta ^ 2 / nu) *
          ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  classical
  let O := ball center r
  let pp := ENNReal.ofReal (2 * alpha)
  let qq := ENNReal.ofReal (2 * alpha / (2 * alpha - 1))
  have hp0 : 0 < 2 * alpha := by linarith
  have hd0 : 0 < 2 * alpha - 1 := by linarith
  have hpp : 1 ≤ pp := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (by linarith : 1 ≤ 2 * alpha)
  have hqq : 1 ≤ qq := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal
      ((le_div_iff₀ hd0).mpr (by linarith : 1 * (2 * alpha - 1) ≤ 2 * alpha))
  let : ENNReal.HolderConjugate qq pp := ENNReal.HolderTriple.of_toReal (by
    simp only [qq, pp, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (div_pos hp0 hd0).le]
    exact ⟨by field_simp; ring, div_pos hp0 hd0, hp0⟩)
  let q (x : LoopPlane) := (V 0 x, V 1 x)
  let H := O.indicator (fun x => (1 + ‖q x‖ ^ 2) ^ alpha)
  let W := O.indicator (fun x => (1 + ‖q x‖ ^ 2) ^ (alpha - 1))
  let F (a : Fin n) (i : Fin 2) := O.indicator (S.flux a i)
  let source (a : Fin n) := O.indicator (S.sourceTerm a)
  obtain ⟨chi, _, _, _, hchi, hcut⟩ := suWeakMap_localization (by linarith : 1 < 2 * alpha)
    hrR S.coordinate_continuous S.coordinate_memLp S.column_memLp S.weak_derivative
  let U (a : Fin n) (x : LoopPlane) := chi x * (u x a - u center a)
  let DU (a : Fin n) (i : Fin 2) (x : LoopPlane) := chi x * V i x a +
    fderiv ℝ chi x (EuclideanSpace.single i 1) * (u x a - u center a)
  have hU (a : Fin n) (x : LoopPlane) (hx : x ∈ O) : U a x = (u x - u center) a := by
    simp only [U, (hchi x hx).1, one_mul, PiLp.sub_apply]
  have hDU (a : Fin n) (i : Fin 2) (x : LoopPlane) (hx : x ∈ O) : DU a i x = V i x a := by
    simp only [DU, (hchi x hx).1, (hchi x hx).2, zero_apply, one_mul, zero_mul, add_zero]
  obtain ⟨hFlux, hSource⟩ := S.flux_source_memLp_of_one_le ha
  have hF (a : Fin n) (i : Fin 2) : MemLp (F a i) qq volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      ((hFlux a i).mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))
  have hsource (a : Fin n) : Integrable (source a) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((hSource a).mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))
  obtain ⟨hWeight, hPotential⟩ := S.canonical_integrability ha
  have hHI : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr
    (hPotential.mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))
  have hWLp : MemLp W (ENNReal.ofReal alpha / ENNReal.ofReal (alpha - 1)) volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      (hWeight.mono_measure (Measure.restrict_mono (ball_subset_ball hrR.le) le_rfl))
  have hWI : Integrable W := hHI.mono' hWLp.1 (MeasureTheory.ae_of_all volume fun x => by
    by_cases hx : x ∈ O
    · simp only [W, H, indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖q x‖ ^ 2) _)]
      exact Real.rpow_le_rpow_of_exponent_le
        (by nlinarith [sq_nonneg ‖q x‖]) (by linarith)
    · simp only [W, H, indicator_of_notMem hx, norm_zero, le_refl])
  have hcross (x : LoopPlane) : (∑ a, ∑ i, F a i x * U a x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 ≤ C ^ 2 * delta ^ 2 * H x * W x *
        ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    by_cases hx : x ∈ O
    · let d (i : Fin 2) := fderiv ℝ phi x (EuclideanSpace.single i 1)
      let w := u x - u center
      let v := (d 0 • w, d 1 • w)
      let A := suAlphaCoordinateFlux g b alpha (x, u x) (q x)
      have hpair : (∑ a, ∑ i, F a i x * U a x * d i) = A v := by
        rw [S.coordinateFlux_pairing]
        apply Finset.sum_congr rfl
        intro a _
        simp only [F, indicator_of_mem hx, hU a x hx, Fin.sum_univ_two, v,
          PiLp.smul_apply, smul_eq_mul, w]
        ring
      have hv : ‖v‖ ^ 2 ≤ delta ^ 2 * (d 0 ^ 2 + d 1 ^ 2) := by
        rw [Prod.norm_def]
        have hnorm (i : Fin 2) : ‖d i • w‖ ^ 2 ≤ delta ^ 2 * (d 0 ^ 2 + d 1 ^ 2) := by
          have ho := pow_le_pow_left₀ (norm_nonneg w) (hosc x hx) 2
          have hi : d i ^ 2 ≤ d 0 ^ 2 + d 1 ^ 2 := by
            fin_cases i <;> dsimp <;> nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]
          simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          nlinarith [mul_le_mul_of_nonneg_left ho (sq_nonneg (d i)),
            mul_le_mul_of_nonneg_left hi (sq_nonneg delta)]
        rcases le_total ‖d 0 • w‖ ‖d 1 • w‖ with hle | hle
        · rw [max_eq_right hle]; exact hnorm 1
        · rw [max_eq_left hle]; exact hnorm 0
      have ha' := pow_le_pow_left₀ (norm_nonneg (A v)) (A.le_opNorm v) 2
      have hm := mul_le_mul (hcoeff x hx).2.1 hv (sq_nonneg _) (by positivity)
      rw [hpair]
      simp only [H, W, indicator_of_mem hx, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs, mul_pow] at ha'
      dsimp only [d, q, A] at hm ha'
      nlinarith
    · simp only [F, H, W, indicator_of_notMem hx, zero_mul, mul_zero,
        Finset.sum_const_zero, zero_pow (by decide : 2 ≠ 0), le_refl]
  have hcoercive (x : LoopPlane) : nu * H x - C0 ≤ ∑ a, ∑ i, F a i x * DU a i x := by
    by_cases hx : x ∈ O
    · simp only [H, F, indicator_of_mem hx, hDU _ _ x hx]
      exact (hcoeff x hx).1.trans_eq (by
        rw [S.coordinateFlux_pairing]
        simp only [Fin.sum_univ_two])
    · simp only [H, F, indicator_of_notMem hx, zero_mul, mul_zero,
        Finset.sum_const_zero, zero_sub]
      exact neg_nonpos.mpr hC0
  have hsourcebound (x : LoopPlane) : (∑ a, source a x * U a x) ≤ C * delta * H x := by
    by_cases hx : x ∈ O
    · simp only [source, H, indicator_of_mem hx, hU _ x hx]
      rw [← S.coordinateSource_pairing]
      have hn := (suAlphaCoordinateSource g b alpha (x, u x) (q x)).le_opNorm (u x - u center)
      have hm := mul_le_mul (hcoeff x hx).2.2 (hosc x hx) (norm_nonneg _) (by positivity)
      change _ ≤ _ at hm
      exact (le_abs_self _).trans (hn.trans hm) |>.trans_eq (by ring)
    · simp only [source, H, indicator_of_notMem hx, zero_mul, Finset.sum_const_zero,
        mul_zero, le_refl]
  have hphi2c : HasCompactSupport (fun x => phi x ^ 2) := hpc.of_isClosed_subset
    (isClosed_tsupport _) (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) phi)
  have hphi2 : MemLp (fun x => phi x ^ 2) ⊤ volume :=
    (hp.continuous.pow 2).memLp_of_hasCompactSupport hphi2c
  have hJ : MemLp (fun x => ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) ⊤ volume := by
    apply memLp_finsetSum
    intro i _
    have hd := (hp.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i (1 : ℝ)))
    exact (hd.pow 2).memLp_of_hasCompactSupport
      ((hpc.fderiv_apply (𝕜 := ℝ) _).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) _))
  have htestW := memLp_one_iff_integrable.mp (hJ.mul' (memLp_one_iff_integrable.mpr hWI))
  refine ⟨htestW, ?_⟩
  exact suNaturalGrowth_potential_bound hpp ENNReal.ofReal_ne_top hqq isOpen_ball hnu hsmall
    (fun x => indicator_nonneg (fun y _ => by positivity) x)
    (fun x => indicator_nonneg (fun y _ => by positivity) x)
    hF hsource (fun a => (hcut a).1) (fun a i => ((hcut a).2.2.2 i).1)
    (fun a i => ((hcut a).2.2.2 i).2) hp hpc hps
    (fun a phi hphi hc hs => S.indicator_equation ha hrR.le a hphi hc hs)
    hcoercive hsourcebound hcross
    (memLp_one_iff_integrable.mp (hphi2.mul' (memLp_one_iff_integrable.mpr hHI))) htestW

set_option maxHeartbeats 800000 in



theorem SUWeakAlphaCoordinate.small_potential
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ ball center r →
      (∫ x in ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha * phi x ^ 2) ≤
        kappa * ∫ x in ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1) *
          ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  classical
  obtain ⟨radius, _, _, hrad, _, _, hrange, _, hshrink⟩ := S.coefficient_neighborhood
  obtain ⟨nu, C, C0, hnu, hC, hC0, hvalue⟩ :=
    suAlphaCoordinate_natural_value_bounds g b ha center S.radius_pos.le (u center) radius hrange
  let T := (8 * C0 + 8 * C ^ 2 / nu) / nu
  have ht : Tendsto (fun t : ℝ => T * t ^ 2) (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using (show Continuous (fun t : ℝ => T * t ^ 2) by fun_prop
      ).continuousAt (x := 0)
  have ht' : Tendsto (fun t : ℝ => C * t) (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using (show Continuous (fun t : ℝ => C * t) by fun_prop
      ).continuousAt (x := 0)
  obtain ⟨eps, heps, he⟩ := Metric.eventually_nhds_iff.mp
    ((ht.eventually (eventually_lt_nhds hkappa)).and
      (ht'.eventually (eventually_lt_nhds (show (0 : ℝ) < nu / 4 by positivity))))
  let delta := eps / 2
  have hdelta : 0 < delta := half_pos heps
  have hd : dist delta 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact half_lt_self heps
  have hds := he hd
  obtain ⟨rho, hrho, hrhoR, hurho⟩ := hshrink delta hdelta
  let r := min rho delta
  have hr : 0 < r := lt_min hrho hdelta
  have hrR : r < R := (min_le_left _ _).trans_lt hrhoR
  have hosc (x : LoopPlane) (hx : x ∈ ball center r) : ‖u x - u center‖ ≤ delta := by
    have hu := hurho (closedBall_subset_closedBall (min_le_left rho delta)
      (ball_subset_closedBall hx))
    exact (show ‖u x - u center‖ < min delta (radius / 2) by
      simpa only [mem_ball, dist_eq_norm] using hu).le.trans (min_le_left _ _)
  have hbase (x : LoopPlane) (hx : x ∈ ball center r) :
      (x, u x) ∈ closedBall center R ×ˢ closedBall (u center) radius := by
    refine ⟨closedBall_subset_closedBall hrR.le (ball_subset_closedBall hx), ?_⟩
    have hu := hurho (closedBall_subset_closedBall (min_le_left rho delta)
      (ball_subset_closedBall hx))
    exact ball_subset_closedBall (ball_subset_ball
      ((min_le_right delta (radius / 2)).trans (half_le_self hrad.le)) hu)
  refine ⟨r, hr, hrR, fun phi hp hpc hps => ?_⟩
  let H := (ball center r).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha)
  let W := (ball center r).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1))
  obtain ⟨hWI, hpot⟩ := alpha_potential_bound S ha hrR hnu hC.le hC0 hdelta.le hds.2.le
    hosc (fun x hx => hvalue (x, u x) (hbase x hx) (V 0 x, V 1 x)) hp hpc hps
  have hW (x : LoopPlane) (hx : x ∈ tsupport phi) : 1 ≤ W x := by
    rw [show W x = (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1) from
      indicator_of_mem (hps hx) _]
    exact Real.one_le_rpow (by nlinarith [sq_nonneg ‖(V 0 x, V 1 x)‖]) (by linarith)
  have hpbound := suNaturalGrowth_local_potential hr hnu hC0 hp hpc hps hW hWI hpot
  have hcoef : (8 * C0 * r ^ 2 + 2 * (4 * C ^ 2 * delta ^ 2 / nu)) / nu ≤ kappa := by
    apply le_trans _ hds.1.le
    apply (div_le_iff₀ hnu).mpr
    have heq : T * delta ^ 2 * nu = (8 * C0 + 8 * C ^ 2 / nu) * delta ^ 2 := by
      dsimp only [T]
      field_simp
    rw [heq]
    have hm := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hr.le (min_le_right rho delta) 2) (by positivity : 0 ≤ 8 * C0)
    calc
      _ ≤ 8 * C0 * delta ^ 2 + 2 * (4 * C ^ 2 * delta ^ 2 / nu) :=
        by linarith only [hm]
      _ = _ := by ring
  have hG : 0 ≤ ∫ x, W x * ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := integral_nonneg fun x =>
    mul_nonneg (indicator_nonneg (fun y _ => by positivity) x)
      (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hfinal := hpbound.trans (mul_le_mul_of_nonneg_right hcoef hG)
  have hHI : (∫ x, H x * phi x ^ 2) =
      ∫ x in ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha * phi x ^ 2 := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ ball center r
    · simp only [H, indicator_of_mem hx]
    · simp only [H, indicator_of_notMem hx, zero_mul]
  have hGI : (∫ x, W x * ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ x in ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1) *
        ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ ball center r
    · simp only [W, indicator_of_mem hx]
    · simp only [W, indicator_of_notMem hx, zero_mul]
  rwa [hHI, hGI] at hfinal

end PoincareConjecture.M60
