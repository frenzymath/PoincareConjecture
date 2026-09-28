import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalRegularity









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak

noncomputable section

namespace PoincareConjecture.M60

namespace SUQuadraticWeakSystem

variable {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
  {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}

set_option maxHeartbeats 800000 in




theorem potential_bound (S : SUQuadraticWeakSystem u V center R)
    {r delta : ℝ} (_hr : 0 < r) (hrR : r < R) (hdelta : 0 ≤ delta)
    (hosc : ∀ x ∈ Metric.ball center r, ‖u x - u center‖ ≤ delta)
    (hsmall : 2 * S.constant * delta ≤ S.nu / 8)
    {phi : LoopPlane → ℝ} (hphi : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
    (hs : tsupport phi ⊆ Metric.ball center r) :
    S.nu / 4 * (∫ x in Metric.ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) * phi x ^ 2) ≤
      (S.nu / 2 + S.constant ^ 2 / S.nu) * (∫ x, phi x ^ 2) +
      (32 * S.constant ^ 2 * delta ^ 2 / S.nu) *
        ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  classical
  let O := Metric.ball center r
  let mu := volume.restrict (Metric.ball center R)
  let : IsFiniteMeasure mu := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  let q (x : LoopPlane) := (V 0 x, V 1 x)
  let H := O.indicator (fun x => 1 + ‖q x‖ ^ 2)
  let W := O.indicator (fun _ => (1 : ℝ))
  let F (a : Fin m) (i : Fin 2) := O.indicator (S.componentFlux a i)
  let b (a : Fin m) := O.indicator (S.componentSource a)
  let C0 := S.nu / 2 + S.constant ^ 2 / S.nu
  obtain ⟨chi, _, _, _, hchiEq, hcut⟩ := suWeakMap_localization
    (p := 2) (by norm_num) hrR S.coordinate_continuous
    (by simpa only [ENNReal.ofReal_ofNat] using S.coordinate_memLp)
    (fun i => by simpa only [ENNReal.ofReal_ofNat] using S.column_memLp i) S.weak_derivative
  simp only [ENNReal.ofReal_ofNat] at hcut
  let U (a : Fin m) (x : LoopPlane) := chi x * (u x a - u center a)
  let DU (a : Fin m) (i : Fin 2) (x : LoopPlane) := chi x * V i x a +
    fderiv ℝ chi x (EuclideanSpace.single i 1) * (u x a - u center a)
  have hU (a : Fin m) (x : LoopPlane) (hx : x ∈ O) : U a x = (u x - u center) a := by
    simp only [U, (hchiEq x hx).1, one_mul, PiLp.sub_apply]
  have hDU (a : Fin m) (i : Fin 2) (x : LoopPlane) (hx : x ∈ O) : DU a i x = V i x a := by
    simp only [DU, (hchiEq x hx).1, (hchiEq x hx).2, zero_apply, one_mul, zero_mul, add_zero]
  have hF (a : Fin m) (i : Fin 2) : MemLp (F a i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      ((S.component_memLp.1 a i).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl))
  have hb (a : Fin m) : Integrable (b a) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((S.component_memLp.2 a).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl))
  have hH : Integrable H := by
    have hq : MemLp q 2 mu := memLp_prod_iff.mpr ⟨S.column_memLp 0, S.column_memLp 1⟩
    have hsq : MemLp (fun x => ‖q x‖ ^ 2) 1 mu := by
      simpa only [pow_two] using hq.norm.mul' hq.norm
    exact (integrable_indicator_iff measurableSet_ball).mpr
      ((memLp_one_iff_integrable.mp ((memLp_const (1 : ℝ)).add hsq)).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrR.le) le_rfl))
  have hWI : MemLp W ⊤ volume :=
    memLp_indicator_const ⊤ measurableSet_ball 1 (Or.inr measure_ball_lt_top.ne)
  have hcross (x : LoopPlane) : (∑ a, ∑ i, F a i x * U a x *
      fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 ≤
      (2 * S.constant) ^ 2 * delta ^ 2 * H x * W x *
        ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    by_cases hx : x ∈ O
    · let d (i : Fin 2) := fderiv ℝ phi x (EuclideanSpace.single i 1)
      let w := u x - u center
      let v := (d 0 • w, d 1 • w)
      let A := S.flux (x, u x) (q x)
      have hpair : (∑ a, ∑ i, F a i x * U a x * d i) = A v := by
        have hp := suColumnDual_pairing A (fun i => d i • w)
        convert hp using 1
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro i _
        simp only [F, indicator_of_mem hx, hU a x hx, componentFlux, PiLp.smul_apply,
          smul_eq_mul, A, q, w]
        ring
      have hv : ‖v‖ ^ 2 ≤ delta ^ 2 * (d 0 ^ 2 + d 1 ^ 2) := by
        have he : ‖v‖ ^ 2 = max (‖d 0 • w‖ ^ 2) (‖d 1 • w‖ ^ 2) := by
          rw [Prod.norm_def]
          rcases le_total ‖d 0 • w‖ ‖d 1 • w‖ with hle | hle
          · rw [max_eq_right hle, max_eq_right (pow_le_pow_left₀ (norm_nonneg _) hle 2)]
          · rw [max_eq_left hle, max_eq_left (pow_le_pow_left₀ (norm_nonneg _) hle 2)]
        rw [he]
        apply max_le
        · have ho := pow_le_pow_left₀ (norm_nonneg w) (hosc x hx) 2
          simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          nlinarith [mul_le_mul_of_nonneg_left ho (sq_nonneg (d 0)),
            mul_nonneg (sq_nonneg delta) (sq_nonneg (d 1))]
        · have ho := pow_le_pow_left₀ (norm_nonneg w) (hosc x hx) 2
          simp only [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
          nlinarith [mul_le_mul_of_nonneg_left ho (sq_nonneg (d 1)),
            mul_nonneg (sq_nonneg delta) (sq_nonneg (d 0))]
      have hAn : ‖A‖ ≤ S.constant * (1 + ‖q x‖) :=
        S.flux_bound _ (S.base_mem (Metric.ball_subset_closedBall
          (Metric.ball_subset_ball hrR.le hx))) _
      have hAv := pow_le_pow_left₀ (norm_nonneg (A v)) (A.le_opNorm v) 2
      have hAn2 := pow_le_pow_left₀ (norm_nonneg A) hAn 2
      have hA2 : ‖A‖ ^ 2 ≤ 4 * S.constant ^ 2 * (1 + ‖q x‖ ^ 2) := by
        have ho : (1 + ‖q x‖) ^ 2 ≤ 4 * (1 + ‖q x‖ ^ 2) := by
          nlinarith [sq_nonneg (‖q x‖ - 1)]
        nlinarith [mul_le_mul_of_nonneg_left ho (sq_nonneg S.constant)]
      have hm := mul_le_mul hA2 hv (sq_nonneg _) (by positivity)
      change _ ≤ _
      rw [hpair]
      simp only [H, W, indicator_of_mem hx, mul_one, Fin.sum_univ_two]
      simp only [Real.norm_eq_abs, sq_abs, mul_pow] at hAv
      dsimp only [d] at hm
      nlinarith
    · simp only [F, H, W, indicator_of_notMem hx, zero_mul, mul_zero, Finset.sum_const_zero,
        ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, le_refl]
  have hcoercive (x : LoopPlane) : S.nu / 2 * H x - C0 ≤ ∑ a, ∑ i, F a i x * DU a i x := by
    by_cases hx : x ∈ O
    · simp only [F, H, indicator_of_mem hx, hDU _ _ x hx, componentFlux]
      rw [suColumnDual_pairing]
      exact S.flux_coercive (S.base_mem (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball hrR.le hx))) (q x)
    · simp only [F, H, indicator_of_notMem hx, zero_mul, mul_zero, Finset.sum_const_zero, zero_sub]
      exact neg_nonpos.mpr (by dsimp [C0]; positivity [S.nu_pos])
  have hsource (x : LoopPlane) : (∑ a, b a x * U a x) ≤ 2 * S.constant * delta * H x := by
    by_cases hx : x ∈ O
    · simp only [b, H, indicator_of_mem hx, hU _ x hx, componentSource]
      rw [suCoordinateDual_pairing]
      have ha := S.source_bound _ (S.base_mem (Metric.ball_subset_closedBall
        (Metric.ball_subset_ball hrR.le hx))) (q x)
      have hn := (S.source (x, u x) (q x)).le_opNorm (u x - u center)
      simp only [Real.norm_eq_abs] at hn
      have hm := mul_le_mul ha (hosc x hx) (norm_nonneg _) (by positivity [S.constant_pos])
      have hp : 0 ≤ S.constant * delta * (1 + ‖q x‖ ^ 2) := by positivity [S.constant_pos]
      change S.source (x, u x) (q x) (u x - u center) ≤ _
      nlinarith [le_abs_self (S.source (x, u x) (q x) (u x - u center))]
    · simp only [b, H, indicator_of_notMem hx, zero_mul, Finset.sum_const_zero, mul_zero, le_refl]
  have hphi2c : HasCompactSupport (fun x => phi x ^ 2) := hc.of_isClosed_subset
    (isClosed_tsupport _) (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) phi)
  have hphi2 : MemLp (fun x => phi x ^ 2) ⊤ volume :=
    (show Continuous (fun x => phi x ^ 2) from hphi.continuous.pow 2
      ).memLp_of_hasCompactSupport hphi2c
  have hGI : Integrable (fun x => ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) := by
    apply integrable_finsetSum
    intro i _
    have hd := (hphi.continuous_fderiv (by simp)).clm_apply
      (continuous_const (y := EuclideanSpace.single i (1 : ℝ)))
    exact (hd.pow 2).integrable_of_hasCompactSupport
      ((hc.fderiv_apply (𝕜 := ℝ) _).of_isClosed_subset (isClosed_tsupport _)
        (tsupport_comp_subset (g := fun t : ℝ => t ^ 2) (by simp) _))
  have he := suNaturalGrowth_potential_bound (p := 2) (q := 2)
    (by norm_num) (by norm_num) (by norm_num) isOpen_ball
    (show 0 < S.nu / 2 by positivity [S.nu_pos]) (by linarith)
    (fun x => indicator_nonneg (fun y _ => by positivity) x)
    (fun x => indicator_nonneg (fun _ _ => zero_le_one) x)
    hF hb (fun a => (hcut a).1) (fun a i => ((hcut a).2.2.2 i).1)
    (fun a i => ((hcut a).2.2.2 i).2) hphi hc hs
    (fun a phi hp hpc hps => S.indicator_equation hrR.le a hp hpc hps)
    hcoercive hsource hcross
    (memLp_one_iff_integrable.mp (hphi2.mul' (memLp_one_iff_integrable.mpr hH)))
    (memLp_one_iff_integrable.mp ((memLp_one_iff_integrable.mpr hGI).mul' hWI))
  have hHI : (∫ x, H x * phi x ^ 2) =
      ∫ x in O, (1 + ‖q x‖ ^ 2) * phi x ^ 2 := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by
      dsimp only [H, O]
      by_cases hx : x ∈ Metric.ball center r <;> simp [hx]
  have hWG : (∫ x, W x * ∑ i : Fin 2,
      (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
      ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    apply integral_congr_ae
    refine Eventually.of_forall fun x => ?_
    by_cases hx : x ∈ O
    · simp only [W, indicator_of_mem hx, one_mul]
    · have hd (i : Fin 2) : fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
          (fun h => hx (hs (tsupport_fderiv_apply_subset ℝ (EuclideanSpace.single i 1) h)))
      simp only [hd, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
  rw [hHI, hWG] at he
  convert he using 1 <;> ring



theorem small_potential (S : SUQuadraticWeakSystem u V center R)
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧ ∀ phi : LoopPlane → ℝ,
      ContDiff ℝ ∞ phi → HasCompactSupport phi → tsupport phi ⊆ Metric.ball center r →
      (∫ x in Metric.ball center r, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) * phi x ^ 2) ≤
        kappa * ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
  let C0 := S.nu / 2 + S.constant ^ 2 / S.nu
  let A := 16 * C0 / S.nu
  let B := 128 * S.constant ^ 2 / S.nu ^ 2
  have hnu := S.nu_pos
  have hC := S.constant_pos
  have hC0 : 0 ≤ C0 := by dsimp [C0]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ht : Tendsto (fun t : ℝ => (A + B) * t ^ 2) (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using (show Continuous (fun t : ℝ => (A + B) * t ^ 2) by fun_prop
      ).continuousAt (x := 0)
  have ht' : Tendsto (fun t : ℝ => 2 * S.constant * t) (𝓝 0) (𝓝 0) := by
    simpa [ContinuousAt] using (show Continuous (fun t : ℝ => 2 * S.constant * t) by fun_prop
      ).continuousAt (x := 0)
  obtain ⟨eps, heps, he⟩ := Metric.eventually_nhds_iff.mp
    ((ht.eventually (eventually_lt_nhds hkappa)).and
      (ht'.eventually (eventually_lt_nhds (show (0 : ℝ) < S.nu / 8 by positivity))))
  let delta := eps / 2
  have hdelta : 0 < delta := half_pos heps
  have hd : dist delta 0 < eps := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hdelta]
    exact half_lt_self heps
  have hds := he hd
  have hu' : ContinuousAt u center := S.coordinate_continuous.continuousAt
    (Metric.closedBall_mem_nhds center S.radius_pos)
  obtain ⟨rho, hrho, hurho⟩ := Metric.continuousAt_iff.mp hu' delta hdelta
  let r := min (R / 2) (min delta (rho / 2))
  have hr : 0 < r := lt_min (half_pos S.radius_pos) (lt_min hdelta (half_pos hrho))
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self S.radius_pos)
  have hrd : r ≤ delta := (min_le_right _ _).trans (min_le_left _ _)
  have hrrho : r < rho := ((min_le_right _ _).trans (min_le_right _ _)).trans_lt
    (half_lt_self hrho)
  have hosc : ∀ x ∈ Metric.ball center r, ‖u x - u center‖ ≤ delta := by
    intro x hx
    simpa only [dist_eq_norm] using (hurho (Metric.mem_ball.mp hx |>.trans hrrho)).le
  have hcoef : A * r ^ 2 + B * delta ^ 2 < kappa := by
    have hr2 := pow_le_pow_left₀ hr.le hrd 2
    have hm := mul_le_mul_of_nonneg_left hr2 hA
    nlinarith [hds.1]
  refine ⟨r, hr, hrR, fun phi hp hpc hps => ?_⟩
  have hpot := S.potential_bound hr hrR hdelta.le hosc hds.2.le hp hpc hps
  have hpi := mul_le_mul_of_nonneg_left (suSmoothCutoff_poincare hr hp hpc hps) hC0
  let G := ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2
  have hG : 0 ≤ G := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hc : 16 * C0 * r ^ 2 + 128 * S.constant ^ 2 * delta ^ 2 / S.nu < kappa * S.nu := by
    have hm := mul_lt_mul_of_pos_right hcoef hnu
    have heq : (A * r ^ 2 + B * delta ^ 2) * S.nu =
        16 * C0 * r ^ 2 + 128 * S.constant ^ 2 * delta ^ 2 / S.nu := by
      dsimp only [A, B]
      field_simp [hnu.ne']
    rwa [heq] at hm
  have hm := mul_le_mul_of_nonneg_right hc.le hG
  change S.nu / 4 * _ ≤ C0 * _ + _ * G at hpot
  change C0 * _ ≤ C0 * (4 * r ^ 2 * G) at hpi
  change _ ≤ kappa * G
  have he : (128 * S.constant ^ 2 * delta ^ 2 / S.nu) * G =
      4 * ((32 * S.constant ^ 2 * delta ^ 2 / S.nu) * G) := by ring
  nlinarith



theorem difference_integrand (S : SUQuadraticWeakSystem u V center R)
    (k : Fin 2) {h : ℝ} (hh : h ≠ 0) (x : LoopPlane)
    (hx : x ∈ Metric.closedBall center R)
    (hy : x + h • EuclideanSpace.single k 1 ∈ Metric.closedBall center R)
    (xi : ℝ) (dx : Fin 2 → ℝ) :
    let H := 2 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
      V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2 + ‖(V 0 x, V 1 x)‖ ^ 2
    S.nu / 4 * (∑ a : Fin m, ∑ i : Fin 2,
      (xi * diffQuot k h (fun z => V i z a) x) ^ 2) ≤
      (∑ a : Fin m, ∑ i : Fin 2, diffQuot k h (S.componentFlux a i) x *
        (xi ^ 2 * diffQuot k h (fun z => V i z a) x +
          2 * xi * dx i * diffQuot k h (fun z => u z a) x)) -
      (∑ a : Fin m, diffQuot k h (S.componentSource a) x *
        (xi ^ 2 * diffQuot k h (fun z => u z a) x)) +
      (32 * S.constant ^ 2 / S.nu + 6 * S.constant) *
        ((H * xi ^ 2 + ∑ a : Fin m, H * (xi * diffQuot k h (fun z => u z a) x) ^ 2) +
          ∑ a : Fin m, ∑ i : Fin 2, (dx i * diffQuot k h (fun z => u z a) x) ^ 2) := by
  let y := x + h • EuclideanSpace.single k (1 : ℝ)
  let d (i : Fin 2) := h⁻¹ • (V i y - V i x)
  let w := h⁻¹ • (u y - u x)
  let H := 2 + ‖(V 0 y, V 1 y)‖ ^ 2 + ‖(V 0 x, V 1 x)‖ ^ 2
  let C := 32 * S.constant ^ 2 / S.nu + 6 * S.constant
  let L := h⁻¹ • (S.flux (y, u y) (V 0 y, V 1 y) - S.flux (x, u x) (V 0 x, V 1 x))
  let B := h⁻¹ • (S.source (y, u y) (V 0 y, V 1 y) -
    S.source (x, u x) (V 0 x, V 1 x))
  have hxy : ‖y - x‖ = |h| := by simp [y, norm_smul]
  have huw : u y - u x = h • w := by simp [w, smul_smul, hh]
  have hbase : ‖(y, u y) - (x, u x)‖ ≤ |h| * (1 + ‖w‖) := by
    rw [Prod.norm_def]
    change max ‖y - x‖ ‖u y - u x‖ ≤ _
    rw [hxy, huw, norm_smul, Real.norm_eq_abs]
    exact max_le (by nlinarith [mul_nonneg (abs_nonneg h) (norm_nonneg w)])
      (by nlinarith [abs_nonneg h])
  have hp := S.difference_pointwise (S.base_mem hx) (S.base_mem hy)
    (V 0 y, V 1 y) (V 0 x, V 1 x) (dx 0 • w, dx 1 • w) w
    (xi := xi) hh hbase
  have hprod : h⁻¹ • ((V 0 y, V 1 y) - (V 0 x, V 1 x)) = (d 0, d 1) := rfl
  dsimp only at hp
  rw [hprod] at hp
  have hcol := suNaturalGrowth_column_pointwise L B d w dx
    (nu := S.nu / 2) (H := H) (W := 1) (C := C) (xi := xi)
    (by positivity [S.nu_pos]) (by dsimp [C]; positivity [S.nu_pos, S.constant_pos])
    zero_le_one (by simpa only [one_mul] using hp)
  have hd (i : Fin 2) (a : Fin m) : d i a = diffQuot k h (fun z => V i z a) x := by
    simp only [d, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  have hw (a : Fin m) : w a = diffQuot k h (fun z => u z a) x := by
    simp only [w, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  have hL (a : Fin m) (i : Fin 2) : L (suColumnBasis a i) =
      diffQuot k h (S.componentFlux a i) x := by
    simp only [L, smul_apply, smul_eq_mul, sub_apply,
      diffQuot_apply_of_ne k hh, componentFlux, div_eq_mul_inv, y]
    ring
  have hB (a : Fin m) : B (EuclideanSpace.single a 1) =
      diffQuot k h (S.componentSource a) x := by
    simp only [B, smul_apply, smul_eq_mul, sub_apply,
      diffQuot_apply_of_ne k hh, componentSource, div_eq_mul_inv, y]
    ring
  simp only [hd, hw, hL, hB, one_mul, H, C, y] at hcol
  convert hcol using 1
  ring

set_option maxHeartbeats 1000000 in




theorem uniform_difference_quotients (S : SUQuadraticWeakSystem u V center R) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∃ D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m),
        (∀ i, MemLp (D i) 2 volume) ∧
        (∀ i, EqOn (D i) (V i) (Metric.ball center r)) ∧
        ∃ h0 : ℝ, 0 < h0 ∧ ∃ C : ℝ, ∀ (a : Fin m) (k : Fin 2) (h : ℝ),
          h ≠ 0 → |h| ≤ h0 →
          (∫ x in Metric.ball center r, ∑ i : Fin 2,
            (diffQuot k h (fun y => D i y a) x) ^ 2) ≤ C := by
  classical
  let nu := S.nu / 4
  let B := 32 * S.constant ^ 2 / S.nu + 6 * S.constant
  have hnu : 0 < nu := by dsimp [nu]; positivity [S.nu_pos]
  have hB : 0 < B := by dsimp [B]; positivity [S.nu_pos, S.constant_pos]
  let kappa := nu / (8 * B)
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  have hsmall : 2 * B * (2 * kappa) ≤ nu / 2 := by
    dsimp only [kappa]
    field_simp
    ring_nf
    norm_num
  obtain ⟨rho, hrho, hrhoR, hpot⟩ := S.small_potential hkappa
  let O := Metric.ball center (rho / 2)
  let H := (Metric.ball center rho).indicator (fun x => 1 + ‖(V 0 x, V 1 x)‖ ^ 2)
  let W := (Metric.ball center rho).indicator (fun _ => (1 : ℝ))
  let F (a : Fin m) (i : Fin 2) := (Metric.ball center rho).indicator (S.componentFlux a i)
  let b (a : Fin m) := (Metric.ball center rho).indicator (S.componentSource a)
  obtain ⟨chi, _, _, _, hchi, hcut⟩ := suWeakMap_localization
    (p := 2) (by norm_num) hrhoR S.coordinate_continuous
    (by simpa only [ENNReal.ofReal_ofNat] using S.coordinate_memLp)
    (fun i => by simpa only [ENNReal.ofReal_ofNat] using S.column_memLp i) S.weak_derivative
  simp only [ENNReal.ofReal_ofNat] at hcut
  let U (a : Fin m) (x : LoopPlane) := chi x * (u x a - u center a)
  let DU (a : Fin m) (i : Fin 2) (x : LoopPlane) := chi x * V i x a +
    fderiv ℝ chi x (EuclideanSpace.single i 1) * (u x a - u center a)
  have hU (a : Fin m) (x : LoopPlane) (hx : x ∈ Metric.ball center rho) :
      U a x = u x a - u center a := by simp only [U, (hchi x hx).1, one_mul]
  have hDU (a : Fin m) (i : Fin 2) (x : LoopPlane) (hx : x ∈ Metric.ball center rho) :
      DU a i x = V i x a := by
    simp only [DU, (hchi x hx).1, (hchi x hx).2, zero_apply, one_mul, zero_mul, add_zero]
  have hF (a : Fin m) (i : Fin 2) : MemLp (F a i) 2 volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      ((S.component_memLp.1 a i).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrhoR.le) le_rfl))
  have hb (a : Fin m) : Integrable (b a) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((S.component_memLp.2 a).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrhoR.le) le_rfl))
  have hH : Integrable H := by
    let mu := volume.restrict (Metric.ball center R)
    let : IsFiniteMeasure mu := ⟨by rw [Measure.restrict_apply_univ]; exact measure_ball_lt_top⟩
    have hq : MemLp (fun x => (V 0 x, V 1 x)) 2 mu :=
      memLp_prod_iff.mpr ⟨S.column_memLp 0, S.column_memLp 1⟩
    have hs : MemLp (fun x => ‖(V 0 x, V 1 x)‖ ^ 2) 1 mu := by
      simpa only [pow_two] using hq.norm.mul' hq.norm
    exact (integrable_indicator_iff measurableSet_ball).mpr
      ((memLp_one_iff_integrable.mp ((memLp_const (1 : ℝ)).add hs)).mono_measure
        (Measure.restrict_mono (Metric.ball_subset_ball hrhoR.le) le_rfl))
  have hW : Integrable W := memLp_one_iff_integrable.mp
    (memLp_indicator_const 1 measurableSet_ball 1 (Or.inr measure_ball_lt_top.ne))
  have hH0 (x : LoopPlane) : 0 ≤ H x := indicator_nonneg (fun _ _ => by positivity) x
  have hp0 (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
      (hs : tsupport phi ⊆ Metric.ball center rho) :
      (∫ x, H x * phi x ^ 2) ≤ kappa *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    have hleft : (∫ x, H x * phi x ^ 2) =
        ∫ x in Metric.ball center rho, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) * phi x ^ 2 := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [H]
        by_cases hx : x ∈ Metric.ball center rho <;> simp [hx]
    have hright : (∫ x, W x * ∑ i : Fin 2,
        (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
        ∫ x, ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
      apply integral_congr_ae
      refine Eventually.of_forall fun x => ?_
      by_cases hx : x ∈ Metric.ball center rho
      · simp only [W, indicator_of_mem hx, one_mul]
      · have hd (i : Fin 2) : fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
            (fun ht => hx (hs (tsupport_fderiv_apply_subset ℝ _ ht)))
        simp only [hd, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
    rw [hleft, hright]
    exact hpot phi hp hc hs
  obtain ⟨xi, hxi, hxic, hxi01, hxi1, hxis⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall center (rho / 8)) isOpen_ball
      (Metric.closedBall_subset_ball (by linarith : rho / 8 < rho / 4))
  obtain ⟨C, hC⟩ := suNaturalGrowth_cutoff_remainder_bounded
    (p := 2) (r := ⊤) (t := 1) (u := U) (du := DU)
    (by norm_num) (by norm_num) (show 0 ≤ 2 * kappa by positivity)
    (fun a => (hcut a).1) (fun a => (hcut a).2.1)
    (fun a i => ((hcut a).2.2.2 i).1) (fun a i => ((hcut a).2.2.2 i).2)
    hxi hxic (fun x => (abs_le.mpr ⟨by linarith [(hxi01 ⟨x, rfl⟩).1],
      (hxi01 ⟨x, rfl⟩).2⟩)) hH hH0
    (memLp_top_const (1 / 2 : ℝ))
  let D (i : Fin 2) (x : LoopPlane) : EuclideanSpace ℝ (Fin m) := WithLp.toLp 2 (fun a => DU a i x)
  have hDi (i : Fin 2) : MemLp (D i) 2 volume :=
    MemLp.of_eval_piLp (fun a => ((hcut a).2.2.2 i).1)
  refine ⟨rho / 8, by positivity, by linarith, D, hDi, ?_, rho / 8, by positivity,
    (2 * B / nu) * C, ?_⟩
  · intro i x hx
    ext a
    exact hDU a i x (Metric.ball_subset_ball (by linarith) hx)
  intro a k h hh hhh
  let v := h • EuclideanSpace.single k (1 : ℝ)
  have hv : ‖v‖ = |h| := by simp [v, norm_smul]
  have hxy (x : LoopPlane) (hx : x ∈ O) :
      x ∈ Metric.ball center rho ∧ x + v ∈ Metric.ball center rho := by
    have hd := dist_triangle (x + v) x center
    have he : dist (x + v) x = ‖v‖ := by simp [dist_eq_norm]
    rw [he, hv] at hd
    exact ⟨Metric.ball_subset_ball (by linarith) hx,
      show dist (x + v) center < rho by change dist x center < rho / 2 at hx; linarith⟩
  let Hh := fun x => H x + H (x + v)
  have hHh : Integrable Hh := hH.add
    ((measurePreserving_add_right volume v).integrable_comp_of_integrable hH)
  have hpotential (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi)
      (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
      (∫ x, Hh x * phi x ^ 2) ≤ (2 * kappa) *
        ∫ x, (1 : ℝ) * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    have ht := suNaturalGrowth_translated_potential hH hW hp0
      (a := v) (by rw [hv]; linarith : rho / 2 + ‖v‖ ≤ rho) hp hc hs
    have hwphi (x : LoopPlane) : (W x + W (x + v)) *
        (∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
        2 * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
      by_cases hx : x ∈ O
      · simp only [W, indicator_of_mem (hxy x hx).1, indicator_of_mem (hxy x hx).2]
        norm_num
      · have hd (i : Fin 2) : fderiv ℝ phi x (EuclideanSpace.single i 1) = 0 :=
          image_eq_zero_of_notMem_tsupport
            (f := fun y => fderiv ℝ phi y (EuclideanSpace.single i 1))
            (fun hz => hx (hs (tsupport_fderiv_apply_subset ℝ _ hz)))
        simp only [hd, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero, mul_zero]
    simp_rw [hwphi, one_mul] at ht ⊢
    rw [integral_const_mul] at ht
    exact ht.trans_eq (by ring)
  have hsupp : Metric.cthickening |h| (tsupport xi) ⊆ O := by
    apply (Metric.cthickening_subset_of_subset |h| hxis).trans
    rw [cthickening_ball (abs_nonneg h) (by positivity : 0 < rho / 4)]
    exact Metric.closedBall_subset_ball (by linarith)
  have hpoint (x : LoopPlane) := S.difference_integrand k hh x
  have hxiO : tsupport xi ⊆ O := hxis.trans (Metric.ball_subset_ball (by linarith))
  have hbound := suNaturalGrowth_diffQuot_absorb (p := 2) (q := 2) (r := ⊤) (t := 1)
    (F := F) (b := b) (u := U) (du := DU) (ξ := xi) (H := Hh) (W := fun _ => 1)
    (by norm_num) (by norm_num) (by norm_num) (O := O) isOpen_ball hnu hB.le
    (show 0 ≤ 2 * kappa by positivity) hsmall hHh (memLp_top_const (1 : ℝ)) (fun _ => zero_le_one)
    hF hb (fun a => (hcut a).1) (fun a i => ((hcut a).2.2.2 i).1)
    (fun a i => ((hcut a).2.2.2 i).2) hxi hxic hxiO
    (fun a phi hp hc hs => S.indicator_equation hrhoR.le a hp hc
      (hs.trans (Metric.ball_subset_ball (by linarith : rho / 2 ≤ rho))))
    hpotential k hh hsupp (fun x => ?_)
  · have he := hC k h
    simp only [Poincare.Analysis.Sobolev.translate,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num, one_mul] at he
    simp only [one_mul] at hbound
    have htotal := hbound.trans (mul_le_mul_of_nonneg_left he (by positivity))
    have hI : Integrable (fun x => ∑ a : Fin m, ∑ i : Fin 2,
        (xi x * diffQuot k h (DU a i) x) ^ 2) := by
      apply integrable_finsetSum
      intro a _
      apply integrable_finsetSum
      intro i _
      have hp : MemLp (fun x => xi x * diffQuot k h (DU a i) x) 2 volume :=
        (suWeakMap_diffQuot_memLp (((hcut a).2.2.2 i).1) k h).mul'
          (hxi.continuous.memLp_of_hasCompactSupport hxic : MemLp xi ⊤ volume)
      simpa only [pow_two] using memLp_one_iff_integrable.mp (hp.mul' hp)
    have hIa : Integrable (fun x => ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2) := by
      apply integrable_finsetSum
      intro i _
      have hp : MemLp (fun x => xi x * diffQuot k h (DU a i) x) 2 volume :=
        (suWeakMap_diffQuot_memLp (((hcut a).2.2.2 i).1) k h).mul'
          (hxi.continuous.memLp_of_hasCompactSupport hxic : MemLp xi ⊤ volume)
      simpa only [pow_two] using memLp_one_iff_integrable.mp (hp.mul' hp)
    calc
      _ = ∫ x in Metric.ball center (rho / 8),
          ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        simp only [hxi1 x (Metric.ball_subset_closedBall hx), one_mul]
        rfl
      _ ≤ ∫ x in Metric.ball center (rho / 8),
          ∑ a : Fin m, ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 := by
        exact setIntegral_mono_on hIa.integrableOn hI.integrableOn measurableSet_ball
          (fun x _ => Finset.single_le_sum
            (f := fun b : Fin m => ∑ i : Fin 2, (xi x * diffQuot k h (DU b i) x) ^ 2)
            (fun b _ => Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Finset.mem_univ a))
      _ ≤ ∫ x, ∑ a : Fin m, ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 :=
        setIntegral_le_integral hI (Eventually.of_forall fun x =>
          Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
      _ ≤ _ := by simpa only [one_mul] using htotal
  · by_cases hx : x ∈ tsupport xi
    · have hxy' := hxy x (hxiO hx)
      dsimp only [v] at hxy'
      have hdx (a : Fin m) (i : Fin 2) :
          diffQuot k h (DU a i) x = diffQuot k h (fun y => V i y a) x := by
        simp only [diffQuot_apply_of_ne k hh, hDU a i x hxy'.1, hDU a i _ hxy'.2]
      have hux (a : Fin m) : diffQuot k h (U a) x = diffQuot k h (fun y => u y a) x := by
        simp only [diffQuot_apply_of_ne k hh, hU a x hxy'.1, hU a _ hxy'.2]
        ring
      have hfx (a : Fin m) (i : Fin 2) : diffQuot k h (F a i) x =
          diffQuot k h (S.componentFlux a i) x := by
        simp only [diffQuot_apply_of_ne k hh, F, indicator_of_mem hxy'.1, indicator_of_mem hxy'.2]
      have hbx (a : Fin m) : diffQuot k h (b a) x = diffQuot k h (S.componentSource a) x := by
        simp only [diffQuot_apply_of_ne k hh, b, indicator_of_mem hxy'.1, indicator_of_mem hxy'.2]
      have he := hpoint x
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrhoR.le hxy'.1))
        (Metric.ball_subset_closedBall (Metric.ball_subset_ball hrhoR.le hxy'.2))
        (xi x) (fun i => fderiv ℝ xi x (EuclideanSpace.single i 1))
      have hHhx : Hh x = 2 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
          V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2 + ‖(V 0 x, V 1 x)‖ ^ 2 := by
        simp only [Hh, v, H, indicator_of_mem hxy'.1, indicator_of_mem hxy'.2]
        ring
      simp only [hdx, hux, hfx, hbx, one_mul, hHhx]
      exact he
    · have hz := image_eq_zero_of_notMem_tsupport hx
      have hd (i : Fin 2) : fderiv ℝ xi x (EuclideanSpace.single i 1) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ xi y (EuclideanSpace.single i 1))
          (fun ht => hx (tsupport_fderiv_apply_subset ℝ _ ht))
      simp only [hz, hd, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, add_zero, sub_zero, le_refl]

end SUQuadraticWeakSystem




theorem suQuadraticWeakSystem_initial_gain
    {m : ℕ} {u : LoopPlane → EuclideanSpace ℝ (Fin m)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin m)} {center : LoopPlane} {R : ℝ}
    (S : SUQuadraticWeakSystem u V center R) : Nonempty (SUInitialGain u V center R) := by
  obtain ⟨r, hr, hrR, D, hD, hDV, h0, hh0, C, hbound⟩ := S.uniform_difference_quotients
  have hsub : Metric.ball center r ⊆ Metric.ball center R := Metric.ball_subset_ball hrR.le
  have hw (i : Fin 2) (a : Fin m) : HasWeakPartialDeriv i (fun x => D i x a)
      (fun x => u x a) (Metric.ball center r) := by
    intro phi hp hc hs
    have he := (S.weak_derivative i a).restrict isOpen_ball hsub phi hp hc hs
    rw [he]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hDV i hx]
  obtain ⟨G⟩ := suInitialGain_of_integral_diffQuot_bound hr le_rfl hh0
    (S.coordinate_continuous.mono (Metric.closedBall_subset_closedBall hrR.le))
    (S.coordinate_memLp.mono_measure (Measure.restrict_mono hsub le_rfl)) hD hw
    (fun _ _ => C) hbound
  have hGr : Metric.ball center G.radius ⊆ Metric.ball center r :=
    Metric.ball_subset_ball G.radius_lt.le
  refine ⟨{
    radius := G.radius
    radius_pos := G.radius_pos
    radius_lt := G.radius_lt.trans hrR
    coordinate_continuous := G.coordinate_continuous
    coordinate_memLp := G.coordinate_memLp
    column_memLp := ?_
    weak_derivative := fun i a => (S.weak_derivative i a).restrict isOpen_ball (hGr.trans hsub)
    hessian := G.hessian
    hessian_memLp := G.hessian_memLp
    second_weak_derivative := ?_
  }⟩
  · intro q hq i
    apply (G.column_memLp q hq i).ae_eq
    filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
    exact hDV i (hGr hx)
  · intro i j a phi hp hc hs
    have he := G.second_weak_derivative i j a phi hp hc hs
    rw [← he]
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hDV i (hGr hx)]

end PoincareConjecture.M60
