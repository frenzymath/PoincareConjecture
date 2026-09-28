import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.ExtendFrom










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace PoincareConjecture.M65Boundary

private theorem recovery_sqrt_sq (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  exact Complex.cpow_nat_inv_pow z (by norm_num : (2 : ℕ) ≠ 0)

private theorem recovery_halfDisk_closure {R : ℝ} (hR : 0 < R)
    {x : LoopPlane} (hx : x ∈ closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}) :
    x ∈ closure (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}) := by
  apply Metric.mem_closure_iff.mpr
  intro e he
  let t := min (e / 2) (R / 4)
  have ht : 0 < t := lt_min (half_pos he) (by positivity)
  let v := EuclideanSpace.basisFun (Fin 2) ℝ 1
  have hv : ‖v‖ = 1 := (EuclideanSpace.basisFun (Fin 2) ℝ).norm_eq_one 1
  have htv : ‖t • v‖ = t := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht, hv, mul_one]
  refine ⟨x + t • v, ⟨?_, ?_⟩, ?_⟩
  · rw [mem_ball_zero_iff]
    calc
      ‖x + t • v‖ ≤ ‖x‖ + ‖t • v‖ := norm_add_le _ _
      _ = ‖x‖ + t := by rw [htv]
      _ < R := by
        have hh := mem_closedBall_zero_iff.mp hx.1
        have hh' : t ≤ R / 4 := min_le_right _ _
        linarith
  · change 0 < x 1 + t * v 1
    have hv1 : v 1 = 1 := by simp [v, EuclideanSpace.single]
    rw [hv1, mul_one]
    have hxheight : 0 ≤ x 1 := hx.2
    linarith
  · rw [dist_eq_norm, show x - (x + t • v) = -(t • v) by abel, norm_neg, htv]
    exact (min_le_left _ _).trans_lt (half_lt_self he)

private theorem recovery_root_sign {A : Set LoopPlane} (hA : IsPreconnected A)
    {v q : LoopPlane → ℂ} (hv : ContinuousOn v A) (hq : ContinuousOn q A)
    (hne : ∀ z ∈ A, q z ≠ 0) (hsq : ∀ z ∈ A, v z ^ 2 = q z ^ 2) :
    (EqOn v q A) ∨ EqOn v (fun z => -q z) A := by
  have hcont : ContinuousOn (fun z => (v z / q z).re) A :=
    continuous_re.comp_continuousOn (hv.div hq hne)
  have hvalues (z : LoopPlane) (hz : z ∈ A) :
      v z / q z = 1 ∨ v z / q z = -1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hsq z hz) with h | h
    · left; rw [h, div_self (hne z hz)]
    · right; rw [h, neg_div, div_self (hne z hz)]
  have hreal (z : LoopPlane) (hz : z ∈ A) : (v z / q z).re ≠ 0 := by
    rcases hvalues z hz with h | h <;> simp [h]
  rcases hA.mapsTo_Ioi_or_Iio hcont hreal with h | h
  · left
    intro z hz
    rcases hvalues z hz with he | he
    · exact (div_eq_one_iff_eq (hne z hz)).mp he
    · have hh := h hz
      simp only [mem_Ioi, he, neg_re, one_re] at hh
      linarith
  · right
    intro z hz
    rcases hvalues z hz with he | he
    · have hh := h hz
      simp only [mem_Iio, he, one_re] at hh
      linarith
    · have hh := (div_eq_iff (hne z hz)).mp he
      simpa only [neg_one_mul] using hh

private theorem recovery_square_limit {R : ℝ} (hR : 0 < R)
    {v d : LoopPlane → ℂ}
    (hv : ContinuousOn v (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hd : ContinuousOn d (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hsq : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, v z ^ 2 = d z)
    {x : LoopPlane} (hx : x ∈ closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}) :
    ∃ c : ℂ, Tendsto v (𝓝[ball (0 : LoopPlane) R ∩ {z | 0 < z 1}] x) (𝓝 c) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  have hUS : U ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hxS : x ∈ S := ⟨closedBall_subset_closedBall (by linarith) hx.1, hx.2⟩
  have hdx : Tendsto d (𝓝[U] x) (𝓝 (d x)) := (hd x hxS).mono_left (nhdsWithin_mono _ hUS)
  by_cases hd0 : d x = 0
  · refine ⟨0, tendsto_zero_iff_norm_tendsto_zero.mpr ?_⟩
    have hnorm : Tendsto (fun z => Real.sqrt ‖d z‖) (𝓝[U] x) (𝓝 0) := by
      simpa only [hd0, norm_zero, Real.sqrt_zero] using hdx.norm.sqrt
    apply hnorm.congr'
    filter_upwards [self_mem_nhdsWithin] with z hz
    have heq : ‖v z‖ ^ 2 = ‖d z‖ := by rw [← norm_pow, hsq z hz]
    rw [← heq, Real.sqrt_sq (norm_nonneg _)]
  · let q := fun z => Complex.sqrt (d x) * Complex.sqrt (d z / d x)
    have hquot : ContinuousWithinAt (fun z => (d z / d x).re) S x :=
      continuous_re.continuousAt.comp_continuousWithinAt ((hd x hxS).div_const _)
    have hnear : ∀ᶠ z in 𝓝[S] x, 0 < (d z / d x).re :=
      hquot (isOpen_Ioi.mem_nhds (by simp [hd0]))
    obtain ⟨r, hr, hcap⟩ := Metric.mem_nhdsWithin_iff.mp hnear
    let A := ball x r ∩ U
    have hA : IsPreconnected A := by
      exact ((convex_ball x r).inter ((convex_ball (0 : LoopPlane) R).inter
        (convex_halfSpace_gt (show IsLinearMap ℝ (fun z : LoopPlane => z 1) from
          ⟨fun _ _ => rfl, fun _ _ => rfl⟩) 0))).isPreconnected
    have hq : ContinuousOn q A := by
      apply continuousOn_const.mul
      apply Complex.continuousOn_sqrt.comp ((hd.mono (fun z hz => hUS hz.2)).div_const _)
      intro z hz
      exact Or.inl (hcap ⟨hz.1, hUS hz.2⟩)
    have hq2 (z : LoopPlane) : q z ^ 2 = d z := by
      dsimp only [q]
      rw [mul_pow, recovery_sqrt_sq, recovery_sqrt_sq, mul_div_cancel₀ _ hd0]
    have hqne (z : LoopPlane) (hz : z ∈ A) : q z ≠ 0 := by
      intro hzero
      have hdzero : d z = 0 := by simpa only [hzero, zero_pow two_ne_zero] using (hq2 z).symm
      have hh : 0 < (d z / d x).re := hcap ⟨hz.1, hUS hz.2⟩
      simp only [hdzero, zero_div, zero_re, lt_self_iff_false] at hh
    have hqtend : Tendsto q (𝓝[U] x) (𝓝 (q x)) := by
      apply tendsto_const_nhds.mul
      apply (Complex.continuousAt_sqrt (z := d x / d x) (by simp [hd0])).tendsto.comp
      exact hdx.div_const _
    rcases recovery_root_sign hA (hv.mono inter_subset_right) hq hqne
        (fun z hz => (hsq z hz.2).trans (hq2 z).symm) with heq | heq
    · refine ⟨q x, hqtend.congr' ?_⟩
      filter_upwards [inter_mem_nhdsWithin U (ball_mem_nhds x hr)] with z hz
      exact (heq ⟨hz.2, hz.1⟩).symm
    · refine ⟨-q x, hqtend.neg.congr' ?_⟩
      filter_upwards [inter_mem_nhdsWithin U (ball_mem_nhds x hr)] with z hz
      exact (heq ⟨hz.2, hz.1⟩).symm

private theorem recovery_square_extension {R : ℝ} (hR : 0 < R)
    {v d : LoopPlane → ℂ}
    (hv : ContinuousOn v (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (hd : ContinuousOn d (closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}))
    (hsq : ∀ z ∈ ball (0 : LoopPlane) R ∩ {z | 0 < z 1}, v z ^ 2 = d z) :
    ∃ V : LoopPlane → ℂ,
      ContinuousOn V (closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}) ∧
      EqOn V v (ball 0 (R / 2) ∩ {z | 0 < z 1}) := by
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  refine ⟨extendFrom U v, continuousOn_extendFrom
    (fun x hx => recovery_halfDisk_closure hR hx)
    (fun x hx => recovery_square_limit hR hv hd hsq hx), ?_⟩
  intro x hx
  exact extendFrom_extends hv x ⟨ball_subset_ball (by linarith) hx.1, hx.2⟩

private theorem recovery_completed_square
    (G : LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (hsymm : ∀ v w, G v w = G w v) (e p q : LoopAmbient) (x y : ℝ)
    (ha : G e e ≠ 0)
    (hdiag : G (p + x • e) (p + x • e) = G (q + y • e) (q + y • e))
    (hmixed : G (p + x • e) (q + y • e) = 0) :
    let a : ℂ := G e e
    let b : ℂ := (G e p : ℂ) - I * (G e q : ℂ)
    let c : ℂ := (G p p : ℂ) - (G q q : ℂ) - 2 * I * (G p q : ℂ)
    ((x : ℂ) - I * (y : ℂ) + b / a) ^ 2 = (b / a) ^ 2 - c / a := by
  simp only [map_add, map_smul, add_apply, smul_apply, smul_eq_mul] at hdiag hmixed
  rw [hsymm p e, hsymm q e] at hdiag
  rw [hsymm p e] at hmixed
  let a : ℂ := G e e
  let b : ℂ := (G e p : ℂ) - I * (G e q : ℂ)
  let c : ℂ := (G p p : ℂ) - (G q q : ℂ) - 2 * I * (G p q : ℂ)
  let w : ℂ := (x : ℂ) - I * (y : ℂ)
  have hpoly : a * w ^ 2 + 2 * b * w + c = 0 := by
    apply Complex.ext <;> norm_num [a, b, c, w, pow_two, mul_re, mul_im] <;> nlinarith
  have haC : a ≠ 0 := by
    change (G e e : ℂ) ≠ 0
    exact_mod_cast ha
  change (w + b / a) ^ 2 = (b / a) ^ 2 - c / a
  field_simp
  linear_combination a * hpoly





theorem exists_continuous_full_differential {R : ℝ} (hR : 0 < R)
    (X : LoopPlane → LoopAmbient)
    (hX : ContDiffOn ℝ 1 X (ball (0 : LoopPlane) R ∩ {z | 0 < z 1}))
    (G : LoopPlane → LoopAmbient →L[ℝ] LoopAmbient →L[ℝ] ℝ)
    (hG : ContinuousOn G (closedBall 0 R ∩ {z | 0 ≤ z 1}))
    (hsymm : ∀ z ∈ closedBall 0 R ∩ {z | 0 ≤ z 1}, ∀ v w, G z v w = G z w v)
    (hpos : ∀ z ∈ closedBall 0 R ∩ {z | 0 ≤ z 1}, ∀ v : LoopAmbient,
      v ≠ 0 → 0 < G z v v)
    (hdiag : ∀ z ∈ ball 0 R ∩ {z | 0 < z 1},
      G z (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) =
        G z (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 1))
          (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 1)))
    (hmixed : ∀ z ∈ ball 0 R ∩ {z | 0 < z 1},
      G z (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 0))
          (fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) = 0)
    (j : Fin 3) (T : LoopPlane → Fin 3 → ℂ)
    (hT : ContinuousOn T (closedBall 0 R ∩ {z | 0 ≤ z 1}))
    (hTeq : ∀ z ∈ ball 0 R ∩ {z | 0 < z 1}, ∀ a : Fin 3, a ≠ j →
      T z a = ((fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 0)) a : ℂ) -
        I * ((fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 1)) a : ℂ)) :
    ∃ D : LoopPlane → LoopPlane →L[ℝ] LoopAmbient,
      ContinuousOn D (closedBall 0 (R / 2) ∩ {z | 0 ≤ z 1}) ∧
      EqOn D (fderiv ℝ X) (ball 0 (R / 2) ∩ {z | 0 < z 1}) := by
  classical
  let U := ball (0 : LoopPlane) R ∩ {z | 0 < z 1}
  let S := closedBall (0 : LoopPlane) R ∩ {z | 0 ≤ z 1}
  let K := closedBall (0 : LoopPlane) (R / 2) ∩ {z | 0 ≤ z 1}
  let V := ball (0 : LoopPlane) (R / 2) ∩ {z | 0 < z 1}
  have hUS : U ⊆ S := fun z hz =>
    ⟨ball_subset_closedBall hz.1, (show 0 < z 1 from hz.2).le⟩
  have hKS : K ⊆ S := fun z hz =>
    ⟨closedBall_subset_closedBall (by linarith) hz.1, hz.2⟩
  have hVU : V ⊆ U := fun z hz => ⟨ball_subset_ball (by linarith) hz.1, hz.2⟩
  have hU : IsOpen U := isOpen_ball.inter
    (isOpen_lt continuous_const (EuclideanSpace.proj 1).continuous)
  let e := EuclideanSpace.basisFun (Fin 3) ℝ j
  have he : e ≠ 0 := by
    intro hz
    have hh : ‖e‖ = 1 := (EuclideanSpace.basisFun (Fin 3) ℝ).norm_eq_one j
    simp only [hz, norm_zero, zero_ne_one] at hh
  let v := fun z => fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 0)
  let w := fun z => fderiv ℝ X z (EuclideanSpace.basisFun (Fin 2) ℝ 1)
  let p := fun z => (WithLp.toLp 2 fun a : Fin 3 => if a = j then 0 else (T z a).re : LoopAmbient)
  let q := fun z => (WithLp.toLp 2 fun a : Fin 3 => if a = j then 0 else -(T z a).im : LoopAmbient)
  have hTc (a : Fin 3) : ContinuousOn (fun z => T z a) S :=
    (continuous_apply a).comp_continuousOn hT
  have hp : ContinuousOn p S := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro a
    by_cases haj : a = j
    · simp only [haj, ite_true]; exact continuousOn_const
    · simp only [haj, ite_false]
      exact continuous_re.comp_continuousOn (hTc a)
  have hq : ContinuousOn q S := by
    apply (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
    apply continuousOn_pi.mpr
    intro a
    by_cases haj : a = j
    · simp only [haj, ite_true]; exact continuousOn_const
    · simp only [haj, ite_false]
      exact (continuous_im.comp_continuousOn (hTc a)).neg
  have hv : ContinuousOn v U :=
    (hX.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hw : ContinuousOn w U :=
    (hX.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const
  have hvp (z : LoopPlane) (hz : z ∈ U) : v z = p z + v z j • e := by
    ext a
    by_cases haj : a = j
    · subst a; simp [p, e, EuclideanSpace.single]
    · have hh : (T z a).re = v z a := by
        simpa [v] using congrArg Complex.re (hTeq z hz a haj)
      simp [p, e, EuclideanSpace.single, haj, hh]
  have hwq (z : LoopPlane) (hz : z ∈ U) : w z = q z + w z j • e := by
    ext a
    by_cases haj : a = j
    · subst a; simp [q, e, EuclideanSpace.single]
    · have hh : -(T z a).im = w z a := by
        simpa [w] using congrArg (fun c : ℂ => -c.im) (hTeq z hz a haj)
      simp [q, e, EuclideanSpace.single, haj, hh]
  let a := fun z => (G z e e : ℂ)
  let b := fun z => (G z e (p z) : ℂ) - I * (G z e (q z) : ℂ)
  let c := fun z => (G z (p z) (p z) : ℂ) - (G z (q z) (q z) : ℂ) -
    2 * I * (G z (p z) (q z) : ℂ)
  have ha : ContinuousOn a S := continuous_ofReal.comp_continuousOn
    ((hG.clm_apply continuousOn_const).clm_apply continuousOn_const)
  have hane (z : LoopPlane) (hz : z ∈ S) : a z ≠ 0 := by
    change (G z e e : ℂ) ≠ 0
    exact_mod_cast (ne_of_gt (hpos z hz e he))
  have hb : ContinuousOn b S :=
    (continuous_ofReal.comp_continuousOn ((hG.clm_apply continuousOn_const).clm_apply hp)).sub
      (continuousOn_const.mul
        (continuous_ofReal.comp_continuousOn ((hG.clm_apply continuousOn_const).clm_apply hq)))
  have hc : ContinuousOn c S :=
    ((continuous_ofReal.comp_continuousOn ((hG.clm_apply hp).clm_apply hp)).sub
      (continuous_ofReal.comp_continuousOn ((hG.clm_apply hq).clm_apply hq))).sub
        (continuousOn_const.mul
          (continuous_ofReal.comp_continuousOn ((hG.clm_apply hp).clm_apply hq)))
  let shift := fun z => b z / a z
  let disc := fun z => shift z ^ 2 - c z / a z
  let root := fun z => (v z j : ℂ) - I * (w z j : ℂ) + shift z
  have hshift : ContinuousOn shift S := hb.div ha hane
  have hdisc : ContinuousOn disc S := (hshift.pow 2).sub (hc.div ha hane)
  have hroot : ContinuousOn root U :=
    ((continuous_ofReal.comp_continuousOn
      ((EuclideanSpace.proj j).continuous.comp_continuousOn hv)).sub
      (continuousOn_const.mul (continuous_ofReal.comp_continuousOn
        ((EuclideanSpace.proj j).continuous.comp_continuousOn hw)))).add (hshift.mono hUS)
  have hsq (z : LoopPlane) (hz : z ∈ U) : root z ^ 2 = disc z := by
    have haz : G z e e ≠ 0 := ne_of_gt (hpos z (hUS hz) e he)
    apply recovery_completed_square (G z) (hsymm z (hUS hz)) e (p z) (q z) (v z j) (w z j) haz
    · rw [← hvp z hz, ← hwq z hz]
      exact hdiag z hz
    · rw [← hvp z hz, ← hwq z hz]
      exact hmixed z hz
  obtain ⟨rootBar, hbar, hbareq⟩ := recovery_square_extension hR hroot hdisc hsq
  let W := fun z a => if a = j then rootBar z - shift z else T z a
  have hW : ContinuousOn W K := continuousOn_pi.mpr fun a => by
    by_cases haj : a = j
    · simp only [W, haj, ite_true]
      exact hbar.sub (hshift.mono hKS)
    · simp only [W, haj, ite_false]
      exact (hTc a).mono hKS
  have hWeq (z : LoopPlane) (hz : z ∈ V) (a : Fin 3) :
      W z a = (v z a : ℂ) - I * (w z a : ℂ) := by
    by_cases haj : a = j
    · subst a
      simp only [W, ite_true, hbareq hz, root, add_sub_cancel_right]
    · exact (if_neg haj).trans (hTeq z (hVU hz) a haj)
  let vBar := fun z => (WithLp.toLp 2 fun a : Fin 3 => (W z a).re : LoopAmbient)
  let wBar := fun z => (WithLp.toLp 2 fun a : Fin 3 => -(W z a).im : LoopAmbient)
  have hvBar : ContinuousOn vBar K :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
      (continuousOn_pi.mpr fun a => continuous_re.comp_continuousOn
        ((continuous_apply a).comp_continuousOn hW))
  have hwBar : ContinuousOn wBar K :=
    (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ)).comp_continuousOn
      (continuousOn_pi.mpr fun a => (continuous_im.comp_continuousOn
        ((continuous_apply a).comp_continuousOn hW)).neg)
  let D := fun z =>
    ContinuousLinearMap.smulRightL ℝ LoopPlane LoopAmbient (EuclideanSpace.proj 0) (vBar z) +
      ContinuousLinearMap.smulRightL ℝ LoopPlane LoopAmbient (EuclideanSpace.proj 1) (wBar z)
  refine ⟨D, ?_, ?_⟩
  · exact ((ContinuousLinearMap.smulRightL ℝ LoopPlane LoopAmbient
      (EuclideanSpace.proj 0)).continuous.comp_continuousOn hvBar).add
        ((ContinuousLinearMap.smulRightL ℝ LoopPlane LoopAmbient
          (EuclideanSpace.proj 1)).continuous.comp_continuousOn hwBar)
  · intro z hz
    have hvEq : vBar z = v z := by
      ext a
      change (W z a).re = v z a
      rw [hWeq z hz a]
      simp
    have hwEq : wBar z = w z := by
      ext a
      change -(W z a).im = w z a
      rw [hWeq z hz a]
      simp
    ext y a
    have hy : y = y 0 • EuclideanSpace.basisFun (Fin 2) ℝ 0 +
        y 1 • EuclideanSpace.basisFun (Fin 2) ℝ 1 := by
      ext i
      fin_cases i <;> simp [EuclideanSpace.single]
    change (y 0 • vBar z + y 1 • wBar z) a = (fderiv ℝ X z y) a
    rw [hvEq, hwEq]
    conv_rhs => rw [hy]
    simp only [map_add, map_smul]
    rfl

end PoincareConjecture.M65Boundary
