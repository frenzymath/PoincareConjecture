import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.AlphaCriticalDifferenceQuotient

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory Metric
open scoped Manifold ContDiff Topology ENNReal
open Poincare.Analysis.Sobolev Poincare.Analysis.Sobolev.Weak
open Poincare.Analysis.Elliptic.InteriorEstimates

noncomputable section

namespace PoincareConjecture.M60

namespace SUWeakAlphaCoordinate

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
  {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
  {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}

set_option maxHeartbeats 800000 in

theorem difference_integrand (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (ha : 1 ≤ alpha) :
    ∃ rho nu B : ℝ, 0 < rho ∧ rho < R ∧ 0 < nu ∧ 0 < B ∧
      ∀ (k : Fin 2) (h : ℝ), h ≠ 0 → ∀ x : LoopPlane,
      x ∈ closedBall center rho → x + h • EuclideanSpace.single k 1 ∈ closedBall center rho →
      ∀ (xi : ℝ) (dx : Fin 2 → ℝ),
      let H := (1 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
        V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2) ^ alpha +
          (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha
      let W := (1 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
        V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2) ^ (alpha - 1) +
          (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1)
      nu * (W * ∑ a : Fin n, ∑ i : Fin 2,
        (xi * diffQuot k h (fun z => V i z a) x) ^ 2) ≤
      (∑ a : Fin n, ∑ i : Fin 2, diffQuot k h (S.flux a i) x *
        (xi ^ 2 * diffQuot k h (fun z => V i z a) x +
          2 * xi * dx i * diffQuot k h (fun z => u z a) x)) -
      (∑ a : Fin n, diffQuot k h (S.sourceTerm a) x *
        (xi ^ 2 * diffQuot k h (fun z => u z a) x)) +
      B * ((H * xi ^ 2 + ∑ a : Fin n, H * (xi * diffQuot k h (fun z => u z a) x) ^ 2) +
        W * ∑ a : Fin n, ∑ i : Fin 2, (dx i * diffQuot k h (fun z => u z a) x) ^ 2) := by
  obtain ⟨radius, nu, C, hrad, hnu, hC, _, hshrink, hb⟩ := S.natural_difference_bounds ha
  obtain ⟨rho, hrho, hrhoR, hurho⟩ := hshrink 1 zero_lt_one
  let B := 8 * C ^ 2 / nu + 3 * C
  have hB : 0 < B := by dsimp [B]; positivity
  have hbase (x : LoopPlane) (hx : x ∈ closedBall center rho) :
      (x, u x) ∈ closedBall center R ×ˢ closedBall (u center) radius :=
    ⟨closedBall_subset_closedBall hrhoR.le hx, ball_subset_closedBall
      (ball_subset_ball ((min_le_right _ _).trans (half_le_self hrad.le)) (hurho hx))⟩
  refine ⟨rho, nu / 4, B, hrho, hrhoR, by positivity, hB, ?_⟩
  intro k h hh x hx hy xi dx
  let y := x + h • EuclideanSpace.single k (1 : ℝ)
  let d (i : Fin 2) := h⁻¹ • (V i y - V i x)
  let w := h⁻¹ • (u y - u x)
  let H := (1 + ‖(V 0 y, V 1 y)‖ ^ 2) ^ alpha + (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha
  let W := (1 + ‖(V 0 y, V 1 y)‖ ^ 2) ^ (alpha - 1) +
    (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1)
  let L := h⁻¹ • (suAlphaCoordinateFlux g b alpha (y, u y) (V 0 y, V 1 y) -
    suAlphaCoordinateFlux g b alpha (x, u x) (V 0 x, V 1 x))
  let Z := h⁻¹ • (suAlphaCoordinateSource g b alpha (y, u y) (V 0 y, V 1 y) -
    suAlphaCoordinateSource g b alpha (x, u x) (V 0 x, V 1 x))
  have hxy : ‖y - x‖ = |h| := by simp [y, norm_smul]
  have huw : u y - u x = h • w := by simp [w, smul_smul, hh]
  have hdist : ‖(y, u y) - (x, u x)‖ ≤ |h| * (1 + ‖w‖) := by
    rw [Prod.norm_def]
    change max ‖y - x‖ ‖u y - u x‖ ≤ _
    rw [hxy, huw, norm_smul, Real.norm_eq_abs]
    exact max_le (by nlinarith [mul_nonneg (abs_nonneg h) (norm_nonneg w)])
      (by nlinarith [abs_nonneg h])
  obtain ⟨hW, hH, hmono, hP, hA, hZ, hD⟩ :=
    hb (x, u x) (hbase x hx) (y, u y) (hbase y hy) (V 0 y, V 1 y) (V 0 x, V 1 x)
      w h hh hdist
  have hp := suNaturalGrowth_dual_pointwise _ _ _ _ (d 0, d 1) (dx 0 • w, dx 1 • w) w
    (xi := xi) hnu hC.le hW hH hmono hP hA hZ hD
  have hpair :
      h⁻¹ • (suAlphaCoordinateFlux g b alpha (y, u y) (V 0 y, V 1 y) -
        suAlphaCoordinateFlux g b alpha (y, u y) (V 0 x, V 1 x)) +
      h⁻¹ • (suAlphaCoordinateFlux g b alpha (y, u y) (V 0 x, V 1 x) -
        suAlphaCoordinateFlux g b alpha (x, u x) (V 0 x, V 1 x)) = L := by
    rw [← smul_add]
    congr 1
    abel
  have hsource :
      h⁻¹ • (suAlphaCoordinateSource g b alpha (y, u y) (V 0 y, V 1 y) -
        suAlphaCoordinateSource g b alpha (y, u y) (V 0 x, V 1 x)) +
      h⁻¹ • (suAlphaCoordinateSource g b alpha (y, u y) (V 0 x, V 1 x) -
        suAlphaCoordinateSource g b alpha (x, u x) (V 0 x, V 1 x)) = Z := by
    rw [← smul_add]
    congr 1
    abel
  rw [hpair, hsource] at hp
  have hcol := suNaturalGrowth_column_pointwise L Z d w dx
    (nu := nu / 2) (H := H) (W := W) (C := B) (xi := xi)
    (by positivity) hB.le hW hp
  have hd (i : Fin 2) (a : Fin n) : d i a = diffQuot k h (fun z => V i z a) x := by
    simp only [d, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  have hw (a : Fin n) : w a = diffQuot k h (fun z => u z a) x := by
    simp only [w, PiLp.smul_apply, smul_eq_mul, PiLp.sub_apply,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  have hflux (z : LoopPlane) (a : Fin n) (i : Fin 2) :
      suAlphaCoordinateFlux g b alpha (z, u z) (V 0 z, V 1 z) (suColumnBasis a i) =
        S.flux a i z := by
    rw [S.coordinateFlux_pairing]
    fin_cases i <;> simp [suColumnBasis, PiLp.single_apply]
  have hsrc (z : LoopPlane) (a : Fin n) :
      suAlphaCoordinateSource g b alpha (z, u z) (V 0 z, V 1 z) (EuclideanSpace.single a 1) =
        S.sourceTerm a z := by
    rw [S.coordinateSource_pairing]
    simp [PiLp.single_apply]
  have hL (a : Fin n) (i : Fin 2) : L (suColumnBasis a i) = diffQuot k h (S.flux a i) x := by
    simp only [L, smul_apply, smul_eq_mul, sub_apply, hflux,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  have hS (a : Fin n) : Z (EuclideanSpace.single a 1) = diffQuot k h (S.sourceTerm a) x := by
    simp only [Z, smul_apply, smul_eq_mul, sub_apply, hsrc,
      diffQuot_apply_of_ne k hh, div_eq_mul_inv, y]
    ring
  simp only [hd, hw, hL, hS, H, W, y] at hcol
  convert hcol using 1
  ring

set_option maxHeartbeats 1400000 in

theorem uniform_difference_quotients (S : SUWeakAlphaCoordinate g b alpha u V center R)
    (ha : 1 ≤ alpha) :
    ∃ r : ℝ, 0 < r ∧ r < R ∧
      ∃ D : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n),
        (∀ i, MemLp (D i) 2 volume) ∧ (∀ i, EqOn (D i) (V i) (ball center r)) ∧
        ∃ h0 : ℝ, 0 < h0 ∧ ∃ C : ℝ, ∀ (a : Fin n) (k : Fin 2) (h : ℝ),
          h ≠ 0 → |h| ≤ h0 →
          (∫ x in ball center r, ∑ i : Fin 2,
            (diffQuot k h (fun y => D i y a) x) ^ 2) ≤ C := by
  classical
  let pp := ENNReal.ofReal (2 * alpha)
  let qq := ENNReal.ofReal (2 * alpha / (2 * alpha - 1))
  let aa := ENNReal.ofReal alpha
  let rr := aa / ENNReal.ofReal (alpha - 1)
  have ha0 : 0 < alpha := by linarith
  have hp0 : 0 < 2 * alpha := by positivity
  have hd0 : 0 < 2 * alpha - 1 := by linarith
  have h2p : (2 : ℝ≥0∞) ≤ pp := by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal (by linarith : 2 ≤ 2 * alpha)
  have hpp : 1 ≤ pp := (by norm_num : (1 : ℝ≥0∞) ≤ 2).trans h2p
  let : ENNReal.HolderConjugate qq pp := ENNReal.HolderTriple.of_toReal (by
    simp only [qq, pp, ENNReal.toReal_one, ENNReal.toReal_ofReal hp0.le,
      ENNReal.toReal_ofReal (div_pos hp0 hd0).le]
    exact ⟨by field_simp; ring, div_pos hp0 hd0, hp0⟩)
  let : ENNReal.HolderTriple pp pp aa := ENNReal.HolderTriple.of_toReal (by
    simp only [pp, aa, ENNReal.toReal_ofReal ha0.le, ENNReal.toReal_ofReal hp0.le]
    exact ⟨by field_simp; ring, hp0, hp0⟩)
  let : ENNReal.HolderConjugate rr aa := by
    by_cases he : alpha = 1
    · subst alpha
      simp only [rr, aa, sub_self, ENNReal.ofReal_zero, ENNReal.ofReal_one,
        ENNReal.div_zero, ne_eq, one_ne_zero, not_false_eq_true]
      infer_instance
    · have hd : 0 < alpha - 1 := sub_pos.mpr (lt_of_le_of_ne ha (Ne.symm he))
      have ht : rr = ENNReal.ofReal (alpha / (alpha - 1)) :=
        (ENNReal.ofReal_div_of_pos hd).symm
      apply ENNReal.HolderTriple.of_toReal
      simp only [ht, aa, ENNReal.toReal_one,
        ENNReal.toReal_ofReal (div_pos ha0 hd).le, ENNReal.toReal_ofReal ha0.le]
      exact ⟨by field_simp; ring, div_pos ha0 hd, ha0⟩
  let : Fact (1 ≤ rr) := ⟨ENNReal.HolderConjugate.one_le rr aa⟩
  let : Fact (1 ≤ aa) := ⟨by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal ha⟩
  obtain ⟨rho0, nu, B, hrho0, hrho0R, hnu, hB, hpoint⟩ := S.difference_integrand ha
  let kappa := nu / (4 * B)
  have hkappa : 0 < kappa := by dsimp [kappa]; positivity
  have hsmall : 2 * B * kappa ≤ nu / 2 := by
    dsimp only [kappa]
    field_simp
    nlinarith
  obtain ⟨sigma, hsigma, hsigmaR, hpot⟩ := S.small_potential ha hkappa
  let rho := min rho0 sigma
  have hrho : 0 < rho := lt_min hrho0 hsigma
  have hrhoR : rho < R := (min_le_right _ _).trans_lt hsigmaR
  let O := ball center (rho / 2)
  let H := (ball center sigma).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha)
  let W := (ball center sigma).indicator (fun x => (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1))
  let F (a : Fin n) (i : Fin 2) := (ball center sigma).indicator (S.flux a i)
  let source (a : Fin n) := (ball center sigma).indicator (S.sourceTerm a)
  obtain ⟨chi, _, hchic, _, hchi, hcut⟩ := suWeakMap_localization
    (by linarith : 1 < 2 * alpha) hsigmaR S.coordinate_continuous
    S.coordinate_memLp S.column_memLp S.weak_derivative
  let U (a : Fin n) (x : LoopPlane) := chi x * (u x a - u center a)
  let DU (a : Fin n) (i : Fin 2) (x : LoopPlane) := chi x * V i x a +
    fderiv ℝ chi x (EuclideanSpace.single i 1) * (u x a - u center a)
  have hU (a : Fin n) (x : LoopPlane) (hx : x ∈ ball center sigma) :
      U a x = u x a - u center a := by simp only [U, (hchi x hx).1, one_mul]
  have hDU (a : Fin n) (i : Fin 2) (x : LoopPlane) (hx : x ∈ ball center sigma) :
      DU a i x = V i x a := by
    simp only [DU, (hchi x hx).1, (hchi x hx).2, zero_apply, one_mul, zero_mul, add_zero]
  have hDUc (a : Fin n) (i : Fin 2) : HasCompactSupport (DU a i) :=
    hchic.mul_right.add (hchic.fderiv_apply (𝕜 := ℝ) _).mul_right
  have hDU2 (a : Fin n) (i : Fin 2) : MemLp (DU a i) 2 volume :=
    (((hcut a).2.2.2 i).1).mono_exponent_of_measure_support_ne_top
      (fun _ => image_eq_zero_of_notMem_tsupport) (hDUc a i).measure_lt_top.ne h2p
  obtain ⟨hFlux, hSource⟩ := S.flux_source_memLp_of_one_le ha
  have hF (a : Fin n) (i : Fin 2) : MemLp (F a i) qq volume :=
    (memLp_indicator_iff_restrict measurableSet_ball).mpr
      ((hFlux a i).mono_measure (Measure.restrict_mono (ball_subset_ball hsigmaR.le) le_rfl))
  have hsource (a : Fin n) : Integrable (source a) :=
    (integrable_indicator_iff measurableSet_ball).mpr
      ((hSource a).mono_measure (Measure.restrict_mono (ball_subset_ball hsigmaR.le) le_rfl))
  obtain ⟨hWeight, hPotential⟩ := S.canonical_integrability ha
  have hHI : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr
    (hPotential.mono_measure (Measure.restrict_mono (ball_subset_ball hsigmaR.le) le_rfl))
  have hWLp : MemLp W rr volume := (memLp_indicator_iff_restrict measurableSet_ball).mpr
    (hWeight.mono_measure (Measure.restrict_mono (ball_subset_ball hsigmaR.le) le_rfl))
  have hWI : Integrable W := hHI.mono' hWLp.1 (Eventually.of_forall fun x => by
    by_cases hx : x ∈ ball center sigma
    · simp only [W, H, indicator_of_mem hx, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ 1 + ‖(V 0 x, V 1 x)‖ ^ 2) _)]
      exact Real.rpow_le_rpow_of_exponent_le
        (by nlinarith [sq_nonneg ‖(V 0 x, V 1 x)‖]) (by linarith)
    · simp only [W, H, indicator_of_notMem hx, norm_zero, le_refl])
  have hH0 (x : LoopPlane) : 0 ≤ H x := indicator_nonneg (fun _ _ => by positivity) x
  have hW0 (x : LoopPlane) : 0 ≤ W x := indicator_nonneg (fun _ _ => by positivity) x
  have hp0 (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi) (hc : HasCompactSupport phi)
      (hs : tsupport phi ⊆ ball center sigma) :
      (∫ x, H x * phi x ^ 2) ≤ kappa *
        ∫ x, W x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
    have hleft : (∫ x, H x * phi x ^ 2) =
        ∫ x in ball center sigma, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha * phi x ^ 2 := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [H]
        by_cases hx : x ∈ ball center sigma <;> simp [hx]
    have hright : (∫ x, W x * ∑ i : Fin 2,
        (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2) =
        ∫ x in ball center sigma, (1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1) *
          ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 := by
      rw [← integral_indicator measurableSet_ball]
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        dsimp only [W]
        by_cases hx : x ∈ ball center sigma <;> simp [hx]
    rw [hleft, hright]
    exact hpot phi hp hc hs
  obtain ⟨xi, hxi, hxic, hxi01, hxi1, hxis⟩ :=
    NirenbergEuclidean.SmoothEllipticBilinearForm.exists_cutoff
      (isCompact_closedBall center (rho / 8)) isOpen_ball
      (closedBall_subset_ball (by linarith : rho / 8 < rho / 4))
  obtain ⟨C, hC⟩ := suNaturalGrowth_cutoff_remainder_bounded
    (p := pp) (r := rr) (t := aa) (u := U) (du := DU) hpp ENNReal.ofReal_ne_top hkappa.le
    (fun a => (hcut a).1) (fun a => (hcut a).2.1)
    (fun a i => ((hcut a).2.2.2 i).1) (fun a i => ((hcut a).2.2.2 i).2)
    hxi hxic (fun x => (abs_le.mpr ⟨by linarith [(hxi01 ⟨x, rfl⟩).1],
      (hxi01 ⟨x, rfl⟩).2⟩)) hHI hH0 hWLp
  let D (i : Fin 2) (x : LoopPlane) : EuclideanSpace ℝ (Fin n) := WithLp.toLp 2 (fun a => DU a i x)
  have hDi (i : Fin 2) : MemLp (D i) 2 volume := MemLp.of_eval_piLp (fun a => hDU2 a i)
  refine ⟨rho / 8, by positivity, by linarith, D, hDi, ?_, rho / 8, by positivity,
    (2 * B / nu) * C, ?_⟩
  · intro i x hx
    ext a
    exact hDU a i x (ball_subset_ball
      ((show rho / 8 ≤ rho by linarith).trans (min_le_right rho0 sigma)) hx)
  intro a k h hh hhh
  let v := h • EuclideanSpace.single k (1 : ℝ)
  have hv : ‖v‖ = |h| := by simp [v, norm_smul]
  have hxy (x : LoopPlane) (hx : x ∈ O) :
      x ∈ ball center rho ∧ x + v ∈ ball center rho := by
    have hd := dist_triangle (x + v) x center
    have he : dist (x + v) x = ‖v‖ := by simp [dist_eq_norm]
    rw [he, hv] at hd
    exact ⟨ball_subset_ball (by linarith) hx,
      show dist (x + v) center < rho by change dist x center < rho / 2 at hx; linarith⟩
  have hxys (x : LoopPlane) (hx : x ∈ O) :
      x ∈ ball center sigma ∧ x + v ∈ ball center sigma :=
    ⟨ball_subset_ball (min_le_right rho0 sigma) (hxy x hx).1,
      ball_subset_ball (min_le_right rho0 sigma) (hxy x hx).2⟩
  let Hh := fun x => H x + H (x + v)
  let Wh := fun x => W x + W (x + v)
  have hHh : Integrable Hh := hHI.add
    ((measurePreserving_add_right volume v).integrable_comp_of_integrable hHI)
  have hWh : MemLp Wh rr volume := hWLp.add (memLp_translate k h hWLp)
  have hWh0 (x : LoopPlane) : 0 ≤ Wh x := add_nonneg (hW0 x) (hW0 _)
  have hWh1 (x : LoopPlane) (hx : x ∈ O) : 1 ≤ Wh x := by
    have hwx : 1 ≤ W x := by
      simp only [W, indicator_of_mem (hxys x hx).1]
      exact Real.one_le_rpow (by nlinarith [sq_nonneg ‖(V 0 x, V 1 x)‖]) (by linarith)
    exact hwx.trans (le_add_of_nonneg_right (hW0 _))
  have hpotential (phi : LoopPlane → ℝ) (hp : ContDiff ℝ ∞ phi)
      (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ O) :
      (∫ x, Hh x * phi x ^ 2) ≤ kappa *
        ∫ x, Wh x * ∑ i : Fin 2, (fderiv ℝ phi x (EuclideanSpace.single i 1)) ^ 2 :=
    suNaturalGrowth_translated_potential hHI hWI hp0 v
      (by rw [hv]; linarith [min_le_right rho0 sigma] : rho / 2 + ‖v‖ ≤ sigma) hp hc hs
  have hsupp : cthickening |h| (tsupport xi) ⊆ O := by
    apply (cthickening_subset_of_subset |h| hxis).trans
    rw [cthickening_ball (abs_nonneg h) (by positivity : 0 < rho / 4)]
    exact closedBall_subset_ball (by linarith)
  have hxiO : tsupport xi ⊆ O := hxis.trans (ball_subset_ball (by linarith))
  have hbound := suNaturalGrowth_diffQuot_absorb (p := pp) (q := qq) (r := rr) (t := aa)
    (F := F) (b := source) (u := U) (du := DU) (ξ := xi) (H := Hh) (W := Wh)
    hpp ENNReal.ofReal_ne_top (ENNReal.HolderConjugate.one_le qq pp) (O := O) isOpen_ball
    hnu hB.le hkappa.le hsmall hHh hWh hWh0 hF hsource
    (fun a => (hcut a).1) (fun a i => ((hcut a).2.2.2 i).1)
    (fun a i => ((hcut a).2.2.2 i).2) hxi hxic hxiO
    (fun a phi hp hc hs => S.indicator_equation ha hsigmaR.le a hp hc
      (hs.trans (ball_subset_ball
        ((show rho / 2 ≤ rho by linarith).trans (min_le_right rho0 sigma)))))
    hpotential k hh hsupp (fun x => ?_)
  · have he := hC k h
    change (∫ x, Hh x * xi x ^ 2) + (1 + 2 * kappa) *
      (∫ x, Wh x * ∑ a : Fin n, ∑ i : Fin 2,
        (fderiv ℝ xi x (EuclideanSpace.single i 1) * diffQuot k h (U a) x) ^ 2) ≤ C at he
    have htotal := hbound.trans (mul_le_mul_of_nonneg_left he (by positivity))
    have hI : Integrable (fun x => Wh x * ∑ a : Fin n, ∑ i : Fin 2,
        (xi x * diffQuot k h (DU a i) x) ^ 2) := by
      simp_rw [Finset.mul_sum]
      apply integrable_finsetSum
      intro a _
      apply integrable_finsetSum
      intro i _
      have hp : MemLp (fun x => xi x * diffQuot k h (DU a i) x) pp volume :=
        (suWeakMap_diffQuot_memLp (((hcut a).2.2.2 i).1) k h).mul'
          (hxi.continuous.memLp_of_hasCompactSupport hxic : MemLp xi ⊤ volume)
      have hs : MemLp (fun x => (xi x * diffQuot k h (DU a i) x) ^ 2) aa volume := by
        simpa only [pow_two] using hp.mul' hp
      exact memLp_one_iff_integrable.mp (hs.mul' hWh)
    have hIa : Integrable (fun x => ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2) := by
      apply integrable_finsetSum
      intro i _
      have hp : MemLp (fun x => xi x * diffQuot k h (DU a i) x) 2 volume :=
        (suWeakMap_diffQuot_memLp (hDU2 a i) k h).mul'
          (hxi.continuous.memLp_of_hasCompactSupport hxic : MemLp xi ⊤ volume)
      simpa only [pow_two] using memLp_one_iff_integrable.mp (hp.mul' hp)
    calc
      _ = ∫ x in ball center (rho / 8), ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 := by
        apply setIntegral_congr_fun measurableSet_ball
        intro x hx
        simp only [hxi1 x (ball_subset_closedBall hx), one_mul]
        rfl
      _ ≤ ∫ x in ball center (rho / 8), Wh x *
          ∑ a : Fin n, ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 := by
        apply setIntegral_mono_on hIa.integrableOn hI.integrableOn measurableSet_ball
        intro x hx
        have hsum := Finset.single_le_sum
          (f := fun b : Fin n => ∑ i : Fin 2, (xi x * diffQuot k h (DU b i) x) ^ 2)
          (fun b _ => Finset.sum_nonneg (fun i _ => sq_nonneg _)) (Finset.mem_univ a)
        exact hsum.trans (le_mul_of_one_le_left
          (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _)
          (hWh1 x (ball_subset_ball (by linarith : rho / 8 ≤ rho / 2) hx)))
      _ ≤ ∫ x, Wh x * ∑ a : Fin n, ∑ i : Fin 2, (xi x * diffQuot k h (DU a i) x) ^ 2 :=
        setIntegral_le_integral hI (Eventually.of_forall fun x => mul_nonneg (hWh0 x)
          (Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun i _ => sq_nonneg _))
      _ ≤ _ := htotal
  · by_cases hx : x ∈ tsupport xi
    · have hxy' := hxys x (hxiO hx)
      dsimp only [v] at hxy'
      have hdx (a : Fin n) (i : Fin 2) :
          diffQuot k h (DU a i) x = diffQuot k h (fun y => V i y a) x := by
        simp only [diffQuot_apply_of_ne k hh, hDU a i x hxy'.1, hDU a i _ hxy'.2]
      have hux (a : Fin n) : diffQuot k h (U a) x = diffQuot k h (fun y => u y a) x := by
        simp only [diffQuot_apply_of_ne k hh, hU a x hxy'.1, hU a _ hxy'.2]
        ring
      have hfx (a : Fin n) (i : Fin 2) : diffQuot k h (F a i) x =
          diffQuot k h (S.flux a i) x := by
        simp only [diffQuot_apply_of_ne k hh, F, indicator_of_mem hxy'.1, indicator_of_mem hxy'.2]
      have hbx (a : Fin n) : diffQuot k h (source a) x = diffQuot k h (S.sourceTerm a) x := by
        simp only [diffQuot_apply_of_ne k hh, source,
          indicator_of_mem hxy'.1, indicator_of_mem hxy'.2]
      have he := hpoint k h hh x
        (ball_subset_closedBall (ball_subset_ball (min_le_left rho0 sigma) (hxy x (hxiO hx)).1))
        (ball_subset_closedBall (ball_subset_ball (min_le_left rho0 sigma) (hxy x (hxiO hx)).2))
        (xi x) (fun i => fderiv ℝ xi x (EuclideanSpace.single i 1))
      dsimp only at he
      have hWswap := add_comm ((1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ (alpha - 1))
        ((1 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
          V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2) ^ (alpha - 1))
      have hHswap := add_comm ((1 + ‖(V 0 x, V 1 x)‖ ^ 2) ^ alpha)
        ((1 + ‖(V 0 (x + h • EuclideanSpace.single k 1),
          V 1 (x + h • EuclideanSpace.single k 1))‖ ^ 2) ^ alpha)
      simp only [hdx, hux, hfx, hbx, Hh, Wh, H, W, v,
        indicator_of_mem hxy'.1, indicator_of_mem hxy'.2, hWswap, hHswap]
      exact he
    · have hz := image_eq_zero_of_notMem_tsupport hx
      have hd (i : Fin 2) : fderiv ℝ xi x (EuclideanSpace.single i 1) = 0 :=
        image_eq_zero_of_notMem_tsupport
          (f := fun y => fderiv ℝ xi y (EuclideanSpace.single i 1))
          (fun ht => hx (tsupport_fderiv_apply_subset ℝ _ ht))
      simp only [hz, hd, zero_mul, mul_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, add_zero, sub_zero, le_refl]

end SUWeakAlphaCoordinate

theorem suWeakAlphaCoordinate_initial_gain
    {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} {b : M} {alpha : ℝ}
    {u : LoopPlane → EuclideanSpace ℝ (Fin n)}
    {V : Fin 2 → LoopPlane → EuclideanSpace ℝ (Fin n)} {center : LoopPlane} {R : ℝ}
    (S : SUWeakAlphaCoordinate g b alpha u V center R) (ha : 1 ≤ alpha) :
    Nonempty (SUInitialGain u V center R) := by
  obtain ⟨r, hr, hrR, D, hD, hDV, h0, hh0, C, hbound⟩ := S.uniform_difference_quotients ha
  have hsub : ball center r ⊆ ball center R := ball_subset_ball hrR.le
  have hw (i : Fin 2) (a : Fin n) : HasWeakPartialDeriv i (fun x => D i x a)
      (fun x => u x a) (ball center r) := by
    intro phi hp hc hs
    have he := (S.weak_derivative i a).restrict isOpen_ball hsub phi hp hc hs
    rw [he]
    congr 1
    apply setIntegral_congr_fun measurableSet_ball
    intro x hx
    dsimp only
    rw [hDV i hx]
  let : IsFiniteMeasure (volume.restrict (ball center R)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact measure_ball_lt_top⟩
  have hu2 : MemLp u 2 (volume.restrict (ball center R)) := S.coordinate_memLp.mono_exponent (by
    simpa only [ENNReal.ofReal_ofNat] using ENNReal.ofReal_le_ofReal (by linarith : 2 ≤ 2 * alpha))
  obtain ⟨G⟩ := suInitialGain_of_integral_diffQuot_bound hr le_rfl hh0
    (S.coordinate_continuous.mono (closedBall_subset_closedBall hrR.le))
    (hu2.mono_measure (Measure.restrict_mono hsub le_rfl)) hD hw (fun _ _ => C) hbound
  have hGr : ball center G.radius ⊆ ball center r := ball_subset_ball G.radius_lt.le
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
