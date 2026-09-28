import PoincareConjecture.Proofs.M63.Mathlib.PeriodicLabelL2Control
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2Heat
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicGaussianLipschitz
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.Sequences
import Mathlib.Analysis.Complex.OperatorNorm











set_option autoImplicit false

open Set Filter MeasureTheory AddCircle
open scoped Topology ContDiff NNReal

namespace PoincareConjecture.M63





theorem exists_uniform_periodicLabel_subsequence
    {P a b : ℝ} [Fact (0 < P)] (hab : a < b)
    (psi : ℕ → ℝ → ℝ → ℝ) (w : ℕ → ℝ → C(AddCircle P, ℝ))
    (hpsi : ∀ j, ContDiffOn ℝ 1 (Function.uncurry (psi j)) (Icc a b ×ˢ univ))
    (hshift : ∀ j t, t ∈ Icc a b → ∀ x, psi j t (x + P) = psi j t x + P)
    (hw : ∀ j, ContinuousOn (w j) (Ioo a b))
    (htime : ∀ j t, t ∈ Ioo a b → ∀ x,
      HasDerivAt (fun r => psi j r x) (w j t (psi j t x : AddCircle P)) t)
    {ell B U : ℝ} (hell : 0 < ell) (hB : 0 ≤ B)
    (hjac : ∀ j t, t ∈ Icc a b → ∀ x, ell ≤ deriv (psi j t) x)
    (hwnorm : ∀ j t, t ∈ Ioo a b →
      ‖ContinuousMap.toLp 2 haarAddCircle ℝ (w j t)‖ ≤ B)
    (hupper : ∀ j t, t ∈ Icc a b → ∀ x, deriv (psi j t) x ≤ U)
    (hinitial : ∀ j x, psi j a x = x) :
    ∃ (sigma : ℕ → ℕ) (d : ℝ → C(AddCircle P, ℝ)),
      StrictMono sigma ∧ ContinuousOn d (Icc a b) ∧ d a = 0 ∧
      let phi : ℝ → ℝ → ℝ := fun t x => x + d t (x : AddCircle P)
      ContinuousOn (Function.uncurry phi) (Icc a b ×ˢ univ) ∧
      (∀ t ∈ Icc a b, ∀ x, phi t (x + P) = phi t x + P) ∧
      (∀ t ∈ Icc a b, ∀ x y, x ≤ y →
        ell * (y - x) ≤ phi t y - phi t x ∧
          phi t y - phi t x ≤ U * (y - x)) ∧
      ∀ eps > 0, ∃ N : ℕ, ∀ j ≥ N, ∀ t ∈ Icc a b, ∀ x : ℝ,
        |psi (sigma j) t x - phi t x| < eps := by
  classical
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hP : 0 < P := Fact.out
  have hU : 0 ≤ U := hell.le.trans ((hjac 0 a ha 0).trans (hupper 0 a ha 0))
  let k : ℝ≥0 := ⟨U + 1, by positivity⟩
  let C := Real.sqrt ell⁻¹ * B
  have hC : 0 ≤ C := mul_nonneg (Real.sqrt_nonneg _) hB
  obtain ⟨D, V, hDc, hDval, _hVc, _hVval, _hDder, _hVbound, hL2⟩ :=
    exists_periodicLabel_displacement_L2_control hab psi w hpsi hshift hw htime hell hB hjac hwnorm
  let T : C(AddCircle P, ℝ) →L[ℝ] Lp ℝ 2 (haarAddCircle (T := P)) :=
    ContinuousMap.toLp 2 haarAddCircle ℝ
  have hDzero (j : ℕ) : D j a = 0 := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hDval j a ha x, hinitial j x, sub_self]
    rfl
  have hslice (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (psi j t) :=
    (hpsi j).comp_contDiff (f := fun x : ℝ => (t, x))
      (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)
  have hLip (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) :
      LipschitzWith k (fun x : ℝ => D j t (x : AddCircle P)) := by
    have hl : LipschitzWith (⟨U, hU⟩ : ℝ≥0) (psi j t) :=
      lipschitzWith_of_nnnorm_deriv_le ((hslice j t ht).differentiable (by norm_num))
        (fun x => by
          change ‖deriv (psi j t) x‖ ≤ U
          rw [Real.norm_eq_abs, abs_of_nonneg (hell.le.trans (hjac j t ht x))]
          exact hupper j t ht x)
    have heq : (fun x : ℝ => D j t (x : AddCircle P)) = fun x => psi j t x - x :=
      funext (hDval j t ht)
    rw [heq]
    exact hl.sub LipschitzWith.id
  let G := ∫ z : ℝ, ‖(-2 * z) * gaussianHeatKernel 1 z‖
  have hG : 0 ≤ G := integral_nonneg fun _ => norm_nonneg _
  have hheat (f : C(AddCircle P, ℝ)) {r : ℝ≥0}
      (hf : LipschitzWith r (fun x : ℝ => f (x : AddCircle P)))
      (tau : ℝ) (htau : 0 < tau) :
      ‖f‖ ≤ (r : ℝ) * G * Real.sqrt tau +
        ‖periodicL2Heat (L := P) tau htau‖ * ‖T f‖ := by
    let u : C(AddCircle P, ℂ) := Complex.ofRealCLM.compLeftContinuous ℝ (AddCircle P) f
    have hfu : ‖f‖ ≤ ‖u‖ := by
      apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
      intro z
      have hz := ContinuousMap.norm_coe_le_norm u z
      change ‖(f z : ℂ)‖ ≤ ‖u‖ at hz
      simpa only [Complex.norm_real] using hz
    have hu : LipschitzWith r (fun x : ℝ => u (x : AddCircle P)) := by
      change LipschitzWith r (fun x : ℝ => (f (x : AddCircle P) : ℂ))
      simpa only [one_mul, Function.comp_def] using Complex.isometry_ofReal.lipschitz.comp hf
    have hmap : Complex.ofRealCLM.compLpL 2 haarAddCircle (T f) =
        ContinuousMap.toLp 2 haarAddCircle ℂ u := by
      apply Lp.ext
      filter_upwards [Complex.ofRealCLM.coeFn_compLpL (T f),
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) f,
        ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℂ) u] with z hz hy hwz
      rw [hz, hy, hwz]
      rfl
    have hnorm : ‖ContinuousMap.toLp 2 haarAddCircle ℂ u‖ ≤ ‖T f‖ := by
      rw [← hmap]
      calc
        _ ≤ ‖Complex.ofRealCLM.compLpL 2 haarAddCircle‖ * ‖T f‖ :=
          (Complex.ofRealCLM.compLpL 2 haarAddCircle).le_opNorm _
        _ ≤ ‖Complex.ofRealCLM‖ * ‖T f‖ :=
          mul_le_mul_of_nonneg_right Complex.ofRealCLM.norm_compLpL_le (norm_nonneg _)
        _ = _ := by rw [Complex.ofRealCLM_norm, one_mul]
    have herror := periodicGaussianHeat_lipschitz_error_bound u hu htau.le
    have hterm : ‖periodicGaussianHeat tau u‖ ≤
        ‖periodicL2Heat (L := P) tau htau‖ * ‖T f‖ := by
      rw [← periodicL2Heat_eq_gaussian tau htau u]
      exact ((periodicL2Heat tau htau).le_opNorm _).trans
        (mul_le_mul_of_nonneg_left hnorm (norm_nonneg _))
    have htri := norm_sub_le (periodicGaussianHeat tau u)
      (periodicGaussianHeat tau u - u)
    rw [sub_sub_cancel] at htri
    linarith only [hfu, htri, herror, hterm]
  have htimeMod : ∀ eps > 0, ∃ delta > 0, ∀ j s, s ∈ Icc a b →
      ∀ t, t ∈ Icc a b → |t - s| < delta → ‖D j t - D j s‖ < eps := by
    intro eps heps
    let A := ((k + k : ℝ≥0) : ℝ) * G
    have hA : 0 ≤ A := mul_nonneg (k + k).coe_nonneg hG
    let q := eps / (4 * (A + 1))
    have hq : 0 < q := by dsimp only [q]; positivity
    have hqe : 4 * (A + 1) * q = eps := by dsimp only [q]; field_simp
    have hsmall : A * Real.sqrt (q ^ 2) < eps / 2 := by
      rw [Real.sqrt_sq hq.le]
      nlinarith only [hqe, hq, mul_nonneg hA hq.le]
    let H := ‖periodicL2Heat (L := P) (q ^ 2) (sq_pos_of_pos hq)‖
    have hH : 0 ≤ H := norm_nonneg _
    let delta := eps / (4 * (H * C + 1))
    have hd : 0 < delta := by dsimp only [delta]; positivity
    have hde : 4 * (H * C + 1) * delta = eps := by dsimp only [delta]; field_simp
    have hsmall' : H * C * delta < eps / 2 := by
      nlinarith only [hde, hd, mul_nonneg (mul_nonneg hH hC) hd.le]
    refine ⟨delta, hd, ?_⟩
    intro j s hs t ht hst
    have h := hheat (D j t - D j s) ((hLip j t ht).sub (hLip j s hs))
      (q ^ 2) (sq_pos_of_pos hq)
    have hnorm := hL2 j s hs t ht
    have hprod : H * ‖T (D j t - D j s)‖ ≤ H * C * delta := by
      calc
        _ ≤ H * (C * |t - s|) := mul_le_mul_of_nonneg_left hnorm hH
        _ ≤ H * (C * delta) := by gcongr
        _ = _ := (mul_assoc _ _ _).symm
    linarith only [h, hprod, hsmall, hsmall']
  let R := (k : ℝ) * G + ‖periodicL2Heat (L := P) 1 (by norm_num)‖ * C * (b - a)
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have hDbound (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ‖D j t‖ ≤ R := by
    have h := hheat (D j t) (hLip j t ht) 1 (by norm_num)
    have hnorm := hL2 j a ha t ht
    rw [hDzero, sub_zero, abs_of_nonneg (sub_nonneg.mpr ht.1)] at hnorm
    have hb : ‖T (D j t)‖ ≤ C * (b - a) :=
      hnorm.trans (mul_le_mul_of_nonneg_left (sub_le_sub_right ht.2 a) hC)
    simp only [Real.sqrt_one, mul_one] at h
    apply h.trans
    dsimp only [R]
    rw [mul_assoc]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hb (norm_nonneg _))
  let Q (j : ℕ) : C(Icc a b, C(AddCircle P, ℝ)) :=
    ⟨fun t => D j t, continuousOn_iff_continuous_domRestrict.mp (hDc j)⟩
  let X := ↥(Icc a b) × ↥(Icc (0 : ℝ) P)
  let f (j : ℕ) : C(X, ℝ) :=
    ⟨fun z => Q j z.1 (z.2.1 : AddCircle P),
      continuous_eval.comp ((Q j).continuous.comp continuous_fst |>.prodMk
        ((AddCircle.continuous_mk' P).comp (continuous_subtype_val.comp continuous_snd)))⟩
  have hmod : UniformEquicontinuous (fun j => (f j : X → ℝ)) := by
    apply Metric.uniformEquicontinuous_iff.mpr
    intro eps heps
    obtain ⟨delta, hd, hdt⟩ := htimeMod (eps / 2) (by positivity)
    let eta := eps / (4 * ((k : ℝ) + 1))
    have heta : 0 < eta := by dsimp only [eta]; positivity
    have he : 4 * ((k : ℝ) + 1) * eta = eps := by dsimp only [eta]; field_simp
    refine ⟨min delta eta, lt_min hd heta, ?_⟩
    intro z y hzy j
    have ht : |(y.1 : ℝ) - (z.1 : ℝ)| < delta := by
      have h := (le_max_left (dist z.1 y.1) (dist z.2 y.2)).trans_lt hzy
      simpa only [Subtype.dist_eq, Real.dist_eq, abs_sub_comm] using h.trans_le (min_le_left _ _)
    have hx : |(z.2 : ℝ) - (y.2 : ℝ)| < eta := by
      have h := (le_max_right (dist z.1 y.1) (dist z.2 y.2)).trans_lt hzy
      simpa only [Subtype.dist_eq, Real.dist_eq] using h.trans_le (min_le_right _ _)
    have htemp : dist (D j z.1 (z.2.1 : AddCircle P))
        (D j y.1 (z.2.1 : AddCircle P)) < eps / 2 := by
      have h := hdt j z.1 z.1.2 y.1 y.1.2 ht
      have hp := ContinuousMap.norm_coe_le_norm (D j y.1 - D j z.1) (z.2.1 : AddCircle P)
      rw [dist_comm]
      exact (by simpa only [dist_eq_norm, ContinuousMap.sub_apply] using hp.trans_lt h)
    have hsp : dist (D j y.1 (z.2.1 : AddCircle P))
        (D j y.1 (y.2.1 : AddCircle P)) < eps / 2 := by
      have h := (hLip j y.1 y.1.2).dist_le_mul z.2.1 y.2.1
      rw [Real.dist_eq] at h
      have hsmall : (k : ℝ) * eta < eps / 2 := by
        nlinarith only [he, heta, mul_nonneg k.coe_nonneg heta.le]
      exact h.trans_lt ((mul_le_mul_of_nonneg_left hx.le k.coe_nonneg).trans_lt hsmall)
    change dist (D j z.1 (z.2.1 : AddCircle P)) (D j y.1 (y.2.1 : AddCircle P)) < eps
    have htri := dist_triangle (D j z.1 (z.2.1 : AddCircle P))
      (D j y.1 (z.2.1 : AddCircle P)) (D j y.1 (y.2.1 : AddCircle P))
    linarith only [htri, htemp, hsp]
  let e := ContinuousMap.isometryEquivBoundedOfCompact X ℝ
  let fb (j : ℕ) : BoundedContinuousFunction X ℝ := e (f j)
  have hequi : Equicontinuous ((↑) : range fb → X → ℝ) := by
    intro z
    apply Metric.equicontinuousAt_iff.mpr
    intro eps heps
    obtain ⟨delta, hd, hdt⟩ := Metric.uniformEquicontinuous_iff.mp hmod eps heps
    refine ⟨delta, hd, ?_⟩
    intro y hy g
    obtain ⟨j, hj⟩ := g.property
    rw [← hj]
    exact hdt z y (by simpa only [dist_comm] using hy) j
  have hcompact : IsCompact (closure (range fb)) :=
    BoundedContinuousFunction.arzela_ascoli (Metric.closedBall (0 : ℝ) R)
      (isCompact_closedBall 0 R) (range fb)
      (fun g z hg => by
        obtain ⟨j, rfl⟩ := hg
        change dist (D j z.1 (z.2.1 : AddCircle P)) 0 ≤ R
        rw [dist_zero_right]
        exact (ContinuousMap.norm_coe_le_norm _ _).trans (hDbound j z.1 z.1.2)) hequi
  obtain ⟨g, _hg, sigma, hsigma, hconv⟩ := hcompact.tendsto_subseq
    (fun j => subset_closure (mem_range_self j))
  have hpathdist (j m : ℕ) : dist (Q j) (Q m) ≤ dist (fb j) (fb m) := by
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro t
    apply (ContinuousMap.dist_le dist_nonneg).mpr
    intro z
    let x := equivIco P 0 z
    have hx : (x : ℝ) ∈ Icc 0 P :=
      ⟨x.property.1, by simpa only [zero_add] using x.property.2.le⟩
    have hzx : ((x : ℝ) : AddCircle P) = z := coe_equivIco
    have h := BoundedContinuousFunction.dist_coe_le_dist (f := fb j) (g := fb m)
      (t, ⟨x, hx⟩)
    change dist (Q j t z) (Q m t z) ≤ _
    rw [← hzx]
    exact h
  have hqc : CauchySeq (fun j => Q (sigma j)) := by
    apply Metric.cauchySeq_iff.mpr
    intro eps heps
    obtain ⟨N, hN⟩ := Metric.cauchySeq_iff.mp hconv.cauchySeq eps heps
    exact ⟨N, fun j hj m hm => (hpathdist _ _).trans_lt (hN j hj m hm)⟩
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hqc
  let d : ℝ → C(AddCircle P, ℝ) := fun t => if ht : t ∈ Icc a b then q ⟨t, ht⟩ else 0
  have hdval (t : ℝ) (ht : t ∈ Icc a b) : d t = q ⟨t, ht⟩ := dif_pos ht
  have hdc : ContinuousOn d (Icc a b) := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact q.continuous.congr (fun t => (hdval t t.property).symm)
  have hpoint (t : ℝ) (ht : t ∈ Icc a b) (x : ℝ) :
      Tendsto (fun j => psi (sigma j) t x) atTop (𝓝 (x + d t (x : AddCircle P))) := by
    have hev : Tendsto (fun j => Q (sigma j) ⟨t, ht⟩ (x : AddCircle P))
        atTop (𝓝 (q ⟨t, ht⟩ (x : AddCircle P))) :=
      ((continuous_eval_const (x : AddCircle P)).comp
        (continuous_eval_const (⟨t, ht⟩ : Icc a b))).continuousAt.tendsto.comp hq
    have h : Tendsto (fun j => x + Q (sigma j) ⟨t, ht⟩ (x : AddCircle P))
        atTop (𝓝 (x + q ⟨t, ht⟩ (x : AddCircle P))) := tendsto_const_nhds.add hev
    have heq : (fun j => x + Q (sigma j) ⟨t, ht⟩ (x : AddCircle P)) =
        fun j => psi (sigma j) t x := by
      funext j
      change x + D (sigma j) t (x : AddCircle P) = psi (sigma j) t x
      rw [hDval (sigma j) t ht x]
      ring
    rw [heq] at h
    simpa only [hdval t ht] using h
  have hd0 : d a = 0 := by
    ext z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hlim := hpoint a ha x
    simp only [hinitial] at hlim
    have heq : x = x + d a (x : AddCircle P) := tendsto_nhds_unique tendsto_const_nhds hlim
    change d a (x : AddCircle P) = 0
    linarith only [heq]
  refine ⟨sigma, d, hsigma, hdc, hd0, ?_, ?_, ?_, ?_⟩
  · have hp : ContinuousOn (fun z : ℝ × ℝ => (d z.1, (z.2 : AddCircle P)))
        (Icc a b ×ˢ univ) :=
      (hdc.comp continuousOn_fst (fun _ hz => hz.1)).prodMk
        ((AddCircle.continuous_mk' P).comp continuous_snd).continuousOn
    exact continuousOn_snd.add (continuous_eval.comp_continuousOn hp)
  · intro t ht x
    change x + P + d t ((x + P : ℝ) : AddCircle P) = x + d t (x : AddCircle P) + P
    rw [AddCircle.coe_add_period]
    ring
  · intro t ht x y hxy
    have hlim := (hpoint t ht y).sub (hpoint t ht x)
    constructor
    · exact ge_of_tendsto hlim (Eventually.of_forall fun j =>
        mul_sub_le_image_sub_of_le_deriv ((hslice (sigma j) t ht).differentiable (by norm_num))
          (hjac (sigma j) t ht) hxy)
    · exact le_of_tendsto hlim (Eventually.of_forall fun j =>
        image_sub_le_mul_sub_of_deriv_le ((hslice (sigma j) t ht).differentiable (by norm_num))
          (hupper (sigma j) t ht) hxy)
  · intro eps heps
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hq eps heps
    refine ⟨N, ?_⟩
    intro j hj t ht x
    have h := hN j hj
    have htbound := ContinuousMap.dist_apply_le_dist (f := Q (sigma j)) (g := q) ⟨t, ht⟩
    have hxbound := ContinuousMap.dist_apply_le_dist
      (f := Q (sigma j) ⟨t, ht⟩) (g := q ⟨t, ht⟩)
      (x : AddCircle P)
    have hsmall := hxbound.trans htbound |>.trans_lt h
    change dist (D (sigma j) t (x : AddCircle P)) (q ⟨t, ht⟩ (x : AddCircle P)) < eps at hsmall
    rw [Real.dist_eq, hDval (sigma j) t ht x, ← hdval t ht] at hsmall
    simpa only [sub_sub] using hsmall

end PoincareConjecture.M63
