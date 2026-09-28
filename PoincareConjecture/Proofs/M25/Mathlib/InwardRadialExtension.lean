import PoincareConjecture.Proofs.M25.Mathlib.PositiveRadialExtension
import Mathlib.Analysis.SpecialFunctions.Sqrt











set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace Real




theorem exists_smooth_inward_radial_chart
    {f : ℝ → ℝ} {d a b c R : ℝ}
    (hd : 0 < d) (hda : d < a) (hab : a < b)
    (hbc : b < c) (hcR : c < R)
    (hf : ContDiffOn ℝ ∞ f (Ioo d R))
    (hfpos : ∀ r ∈ Ioo d R, 0 < f r)
    (hfderiv : ∀ r ∈ Icc a c, 0 < deriv f r) :
    ∃ (tau : OpenPartialHomeomorph ℝ ℝ) (k : ℝ),
      tau.source = Ioo (-c) c ∧
      tau.target = Ioo (-(f c)) (f c) ∧
      ContDiffOn ℝ ∞ (tau : ℝ → ℝ) tau.source ∧
      ContDiffOn ℝ ∞ tau.symm tau.target ∧
      ContinuousOn (tau : ℝ → ℝ) (Icc (-c) c) ∧
      StrictMonoOn (tau : ℝ → ℝ) (Icc (-c) c) ∧
      (∀ r ∈ tau.source, 0 < deriv (tau : ℝ → ℝ) r) ∧
      tau 0 = 0 ∧ tau.symm 0 = 0 ∧
      EqOn (tau : ℝ → ℝ) f (Icc b c) ∧
      (∀ r ∈ Icc (-c) c, tau (-r) = -tau r) ∧
      tau '' Ioo 0 c = Ioo 0 (f c) ∧
      0 < tau a ∧
      (∀ r ∈ Icc (-a) a,
        0 < 1 + k * r ^ 2 ∧
        tau r = r / Real.sqrt (1 + k * r ^ 2)) ∧
      (∀ r ∈ Icc (-(tau a)) (tau a),
        0 < 1 - k * r ^ 2 ∧
        tau.symm r = r / Real.sqrt (1 - k * r ^ 2)) := by
  classical
  have ha : 0 < a := hd.trans hda
  have hb : 0 < b := ha.trans hab
  have hc : 0 < c := hb.trans hbc
  have hR : 0 < R := hc.trans hcR
  have hac : a < c := hab.trans hbc
  have hdc : d < c := hda.trans hac
  have hRa : -R ^ 2 < -c ^ 2 := by nlinarith
  have hlm : -c ^ 2 < -b ^ 2 := by nlinarith
  have hmu : -b ^ 2 < -a ^ 2 := by nlinarith
  have huU : -a ^ 2 < -d ^ 2 := by nlinarith
  have hu0 : -a ^ 2 < 0 := by nlinarith
  have hl0 : -c ^ 2 < 0 := by nlinarith
  let F : ℝ → ℝ := fun s => (f (sqrt (-s)) ^ 2)⁻¹
  have hsqrt {s : ℝ} (hs : s ∈ Ioo (-R ^ 2) (-d ^ 2)) :
      sqrt (-s) ∈ Ioo d R := by
    refine ⟨(lt_sqrt hd.le).mpr (by linarith [hs.2]), ?_⟩
    exact (sqrt_lt' hR).mpr (by linarith [hs.1])
  have hFsmooth : ContDiffOn ℝ ∞ F (Ioo (-R ^ 2) (-d ^ 2)) := by
    apply isOpen_Ioo.contDiffOn_iff.mpr
    intro s hs
    have hsn : -s ≠ 0 := by nlinarith [sq_nonneg d, hs.2]
    have hsmooth := (contDiffAt_id.neg.sqrt hsn :
      ContDiffAt ℝ ∞ (fun t : ℝ => sqrt (-t)) s)
    exact (((hf.contDiffAt (isOpen_Ioo.mem_nhds (hsqrt hs))).comp s hsmooth).pow 2).inv
      (pow_ne_zero 2 (hfpos _ (hsqrt hs)).ne')
  have hFderiv : ∀ s ∈ Icc (-c ^ 2) (-a ^ 2), 0 < deriv F s := by
    intro s hs
    have hsopen : s ∈ Ioo (-R ^ 2) (-d ^ 2) :=
      ⟨hRa.trans_le hs.1, hs.2.trans_lt huU⟩
    have hsr := hsqrt hsopen
    have hsneg : 0 < -s := by nlinarith [hs.2]
    have hrpos : 0 < sqrt (-s) := sqrt_pos.mpr hsneg
    have hsrclosed : sqrt (-s) ∈ Icc a c := by
      exact ⟨(le_sqrt ha.le hsneg.le).mpr (by linarith [hs.2]),
        (sqrt_le_left hc.le).mpr (by linarith [hs.1])⟩
    have hroot := (hasDerivAt_id s).neg.sqrt hsneg.ne'
    have hcomp := ((hf.contDiffAt (isOpen_Ioo.mem_nhds hsr)).differentiableAt
      (by simp)).hasDerivAt.comp s hroot
    have hinv := (hcomp.pow 2).inv (pow_ne_zero 2 (hfpos _ hsr).ne')
    have heq : deriv F s = deriv f (sqrt (-s)) /
        (sqrt (-s) * f (sqrt (-s)) ^ 3) := by
      rw [show deriv F s = _ from hinv.deriv]
      simp only [Function.comp_apply, Pi.neg_apply, id_eq, Pi.pow_apply,
        Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp [hrpos.ne', (hfpos _ hsr).ne']
    rw [heq]
    exact div_pos (hfderiv _ hsrclosed) (mul_pos hrpos (pow_pos (hfpos _ hsr) 3))
  have hFanchor : 0 < F (-c ^ 2) := by
    dsimp only [F]
    rw [neg_neg, sqrt_sq hc.le]
    exact inv_pos.mpr (sq_pos_of_pos (hfpos c ⟨hdc, hcR⟩))
  let P := positiveRadialPrimitive F (-c ^ 2) (-b ^ 2) (-a ^ 2) 0
  have hPsm : ContDiffOn ℝ ∞ P (Ioo (-R ^ 2) 0) :=
    contDiffOn_positiveRadialPrimitive hmu huU hFsmooth ⟨hRa, hl0⟩
  have hPpos {s : ℝ} (hs : s ∈ Ico (-c ^ 2) 0) : 0 < P s :=
    positiveRadialPrimitive_pos hRa hmu huU hl0 hFsmooth hFderiv hFanchor hs
  have hPderiv {s : ℝ} (hs : s ∈ Ico (-c ^ 2) 0) : 0 < deriv P s :=
    deriv_positiveRadialPrimitive_pos hRa hmu huU hl0 hFsmooth hFderiv hs
  have hPeq : EqOn P F (Icc (-c ^ 2) (-b ^ 2)) :=
    positiveRadialPrimitive_eqOn hRa hmu huU hFsmooth
  let k := P (-a ^ 2) - (a ^ 2)⁻¹
  let U : ℝ → ℝ := fun r => (sqrt (P (-r ^ 2)))⁻¹
  let T : ℝ → ℝ := fun r => if r = 0 then 0 else if 0 < r then U r else -U r
  have hTzero : T 0 = 0 := by simp [T]
  have htrans {r : ℝ} (hr : r ∈ Icc (-c) c) (hne : r ≠ 0) :
      -r ^ 2 ∈ Ico (-c ^ 2) 0 := by
    constructor
    · nlinarith [hr.1, hr.2]
    · nlinarith [sq_pos_of_ne_zero hne]
  have hTodd (r : ℝ) : T (-r) = -T r := by
    have hU : U (-r) = U r := by simp [U]
    rcases lt_trichotomy r 0 with hr | hr | hr
    · simp [T, hr.ne, not_lt.mpr hr.le, neg_pos.mpr hr, hU]
    · simp [hr, T]
    · simp [T, hr.ne', not_lt.mpr (neg_nonpos.mpr hr.le), hr, hU]
  have hcenter (r : ℝ) (hr : r ∈ Icc (-a) a) :
      0 < 1 + k * r ^ 2 ∧ T r = r / sqrt (1 + k * r ^ 2) := by
    by_cases hzero : r = 0
    · simp [hzero, hTzero]
    · have hrc : r ∈ Icc (-c) c := ⟨by linarith [hr.1], hr.2.trans hac.le⟩
      have hrt := htrans hrc hzero
      have hupper : -r ^ 2 ∈ Ico (-a ^ 2) 0 :=
        ⟨by nlinarith [hr.1, hr.2], hrt.2⟩
      have hu := positiveRadialPrimitive_upper_formula hRa hlm hmu huU hu0 hFsmooth hupper
      have hval : P (-r ^ 2) = k + (r ^ 2)⁻¹ := by
        change P (-r ^ 2) = P (-a ^ 2) + (0 - -r ^ 2)⁻¹ - (0 - -a ^ 2)⁻¹ at hu
        simp only [zero_sub, neg_neg] at hu
        dsimp only [k]
        rw [hu]
        ring
      have hfac : 1 + k * r ^ 2 = r ^ 2 * P (-r ^ 2) := by
        rw [hval]
        field_simp
        ring
      have hpos : 0 < 1 + k * r ^ 2 := by
        rw [hfac]
        exact mul_pos (sq_pos_of_ne_zero hzero) (hPpos hrt)
      refine ⟨hpos, ?_⟩
      rw [hfac, sqrt_mul (sq_nonneg r), sqrt_sq_eq_abs]
      rcases lt_or_gt_of_ne hzero with hrneg | hrpos
      · simp only [T, if_neg hzero, if_neg (not_lt.mpr hrneg.le), U, abs_of_neg hrneg]
        field_simp
      · simp only [T, if_neg hzero, if_pos hrpos, U, abs_of_pos hrpos]
        field_simp
  have hUnonzero (r : ℝ) (hr : r ∈ Icc (-c) c) (hne : r ≠ 0) :
      ContDiffAt ℝ ∞ U r ∧
      HasDerivAt U (r * deriv P (-r ^ 2) /
        (P (-r ^ 2) * sqrt (P (-r ^ 2)))) r := by
    have hrt := htrans hr hne
    have hps : ContDiffAt ℝ ∞ P (-r ^ 2) :=
      hPsm.contDiffAt (isOpen_Ioo.mem_nhds ⟨hRa.trans_le hrt.1, hrt.2⟩)
    have hpp := hPpos hrt
    have hbase : ContDiffAt ℝ ∞ (fun t : ℝ => P (-t ^ 2)) r :=
      hps.comp (g := P) (f := fun t : ℝ => -t ^ 2) r (contDiffAt_id.pow 2).neg
    refine ⟨(hbase.sqrt hpp.ne').inv (sqrt_pos.mpr hpp).ne', ?_⟩
    have hdp : HasDerivAt P (deriv P (-r ^ 2)) (-r ^ 2) :=
      (hps.differentiableAt (by simp)).hasDerivAt
    have hcomp : HasDerivAt (fun t : ℝ => P (-t ^ 2))
        (deriv P (-r ^ 2) * (-(2 * r))) r := by
      convert! hdp.comp r ((hasDerivAt_id r).pow 2).neg using 1
      simp
    have hder := hcomp.sqrt hpp.ne'
    have hinv := hder.inv (sqrt_pos.mpr hpp).ne'
    convert! hinv using 1
    rw [sq_sqrt hpp.le]
    field_simp
  have hTsmooth (r : ℝ) (hr : r ∈ Icc (-c) c) : ContDiffAt ℝ ∞ T r := by
    by_cases hzero : r = 0
    · subst r
      have hform : ContDiffAt ℝ ∞ (fun t : ℝ => t / sqrt (1 + k * t ^ 2)) 0 :=
        contDiffAt_id.div ((contDiffAt_const.add (contDiffAt_const.mul
          (contDiffAt_id.pow 2))).sqrt (by norm_num)) (by norm_num)
      apply hform.congr_of_eventuallyEq
      filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr ha) ha] with s hs
      exact (hcenter s ⟨hs.1.le, hs.2.le⟩).2
    · have hu := (hUnonzero r hr hzero).1
      rcases lt_or_gt_of_ne hzero with hn | hp
      · apply hu.neg.congr_of_eventuallyEq
        filter_upwards [Iio_mem_nhds hn] with s hs
        change s < 0 at hs
        simp only [T, if_neg hs.ne, if_neg (not_lt.mpr hs.le)]
      · apply hu.congr_of_eventuallyEq
        filter_upwards [Ioi_mem_nhds hp] with s hs
        change 0 < s at hs
        simp only [T, if_neg hs.ne', if_pos hs]
  have hTderiv (r : ℝ) (hr : r ∈ Icc (-c) c) : 0 < deriv T r := by
    by_cases hzero : r = 0
    · subst r
      have hform : HasDerivAt (fun t : ℝ => t / sqrt (1 + k * t ^ 2)) 1 0 := by
        convert! (hasDerivAt_id (0 : ℝ)).div
          (((hasDerivAt_const 0 (1 : ℝ)).add
            (((hasDerivAt_id (0 : ℝ)).pow 2).const_mul k)).sqrt (by norm_num))
          (by norm_num) using 1
        norm_num
      have heq : T =ᶠ[𝓝 (0 : ℝ)] fun t => t / sqrt (1 + k * t ^ 2) := by
        filter_upwards [Ioo_mem_nhds (neg_lt_zero.mpr ha) ha] with s hs
        exact (hcenter s ⟨hs.1.le, hs.2.le⟩).2
      rw [(hform.congr_of_eventuallyEq heq).deriv]
      norm_num
    · have hu := (hUnonzero r hr hzero).2
      have hp := hPpos (htrans hr hzero)
      have hdP := hPderiv (htrans hr hzero)
      rcases lt_or_gt_of_ne hzero with hn | hpos
      · have heq : T =ᶠ[𝓝 r] fun t => -U t := by
          filter_upwards [Iio_mem_nhds hn] with s hs
          change s < 0 at hs
          simp only [T, if_neg hs.ne, if_neg (not_lt.mpr hs.le)]
        rw [(hu.neg.congr_of_eventuallyEq heq).deriv]
        exact neg_pos.mpr (div_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn hdP)
          (mul_pos hp (sqrt_pos.mpr hp)))
      · have heq : T =ᶠ[𝓝 r] U := by
          filter_upwards [Ioi_mem_nhds hpos] with s hs
          change 0 < s at hs
          simp only [T, if_neg hs.ne', if_pos hs]
        rw [(hu.congr_of_eventuallyEq heq).deriv]
        exact div_pos (mul_pos hpos hdP) (mul_pos hp (sqrt_pos.mpr hp))
  have hTcont : ContinuousOn T (Icc (-c) c) :=
    fun r hr => (hTsmooth r hr).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn T (Icc (-c) c) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hTcont
      (fun r hr => hTderiv r (interior_subset hr))
  have hmatch : EqOn T f (Icc b c) := by
    intro r hr
    have hrpos : 0 < r := hb.trans_le hr.1
    have harg : -r ^ 2 ∈ Icc (-c ^ 2) (-b ^ 2) := by
      constructor <;> nlinarith [hr.1, hr.2]
    rw [show T r = U r by simp only [T, if_neg hrpos.ne', if_pos hrpos]]
    dsimp only [U]
    rw [hPeq harg]
    dsimp only [F]
    rw [neg_neg, sqrt_sq hrpos.le, sqrt_inv, sqrt_sq (hfpos r ⟨hda.trans (hab.trans_le hr.1),
      hr.2.trans_lt hcR⟩).le, inv_inv]
  have hTc : T c = f c := hmatch ⟨hbc.le, le_rfl⟩
  have hTnc : T (-c) = -(f c) := (hTodd c).trans (congrArg Neg.neg hTc)
  have himage : T '' Ioo (-c) c = Ioo (-(f c)) (f c) := by
    simpa only [hTc, hTnc] using
      hTcont.image_Ioo_of_strictMonoOn (by linarith : -c ≤ c) hmono
  have hhalf : T '' Ioo 0 c = Ioo 0 (f c) := by
    simpa only [hTzero, hTc] using
      (hTcont.mono (show Icc 0 c ⊆ Icc (-c) c from fun r hr =>
        ⟨by linarith [hr.1], hr.2⟩)).image_Ioo_of_strictMonoOn hc.le
        (hmono.mono (fun r hr => ⟨by linarith [hr.1], hr.2⟩))
  have hmono' : StrictMonoOn T (Ioo (-c) c) := hmono.mono Ioo_subset_Icc_self
  have hstrict : StrictMono ((Ioo (-c) c).domRestrict T) :=
    fun x y hxy => hmono' x.property y.property hxy
  have hrange : range ((Ioo (-c) c).domRestrict T) = Ioo (-(f c)) (f c) := by
    rw [range_domRestrict, himage]
  have hemb := hstrict.isEmbedding_of_ordConnected (by rw [hrange]; infer_instance)
  have hopen : Topology.IsOpenEmbedding ((Ioo (-c) c).domRestrict T) :=
    ⟨hemb, by rw [hrange]; exact isOpen_Ioo⟩
  let pe := Set.InjOn.toPartialEquiv T (Ioo (-c) c) hmono'.injOn
  let tau := OpenPartialHomeomorph.ofContinuousOpenRestrict pe
    (hTcont.mono Ioo_subset_Icc_self) hopen.isOpenMap isOpen_Ioo
  have hsource : tau.source = Ioo (-c) c := rfl
  have htarget : tau.target = Ioo (-(f c)) (f c) := himage
  have htau (r : ℝ) : tau r = T r := rfl
  have htauSm : ContDiffOn ℝ ∞ (tau : ℝ → ℝ) tau.source :=
    fun r hr => (hTsmooth r ⟨hr.1.le, hr.2.le⟩).contDiffWithinAt
  have hiSm : ContDiffOn ℝ ∞ tau.symm tau.target := by
    intro y hy
    have hx := tau.map_target hy
    have hsm := hTsmooth (tau.symm y) ⟨hx.1.le, hx.2.le⟩
    exact (tau.contDiffAt_symm_deriv
      (hTderiv (tau.symm y) ⟨hx.1.le, hx.2.le⟩).ne' hy
      (hsm.differentiableAt (by simp)).hasDerivAt hsm).contDiffWithinAt
  have hzeroSource : (0 : ℝ) ∈ tau.source := ⟨by linarith, hc⟩
  have hzeroInv : tau.symm 0 = 0 := by
    simpa only [htau, hTzero] using tau.left_inv hzeroSource
  have haSource : a ∈ tau.source := ⟨by linarith, hac⟩
  have htaPos : 0 < tau a := by
    change 0 < T a
    rw [← hTzero]
    exact hmono ⟨by linarith, hc.le⟩ ⟨by linarith, hac.le⟩ ha
  refine ⟨tau, k, hsource, htarget, htauSm, hiSm, hTcont, hmono,
    (fun r hr => hTderiv r ⟨hr.1.le, hr.2.le⟩), hTzero, hzeroInv,
    hmatch, (fun r _ => hTodd r), hhalf, htaPos, hcenter, ?_⟩
  intro y hy
  have htaUpper : tau a < f c := by
    rw [htau, ← hTc]
    exact hmono ⟨by linarith, hac.le⟩ ⟨by linarith, le_rfl⟩ hac
  have hyTarget : y ∈ tau.target := by
    rw [htarget]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  let x := tau.symm y
  have hxSource : x ∈ tau.source := tau.map_target hyTarget
  have hxy : tau x = y := tau.right_inv hyTarget
  have hxCenter : x ∈ Icc (-a) a := by
    constructor
    · by_contra hn
      have hlt := hmono ⟨hxSource.1.le, hxSource.2.le⟩
        (show -a ∈ Icc (-c) c from ⟨by linarith, by linarith⟩) (lt_of_not_ge hn)
      rw [← htau x, hxy, hTodd a, ← htau a] at hlt
      exact (not_lt_of_ge hy.1) hlt
    · by_contra hn
      have hlt := hmono (show a ∈ Icc (-c) c from ⟨by linarith, hac.le⟩)
        ⟨hxSource.1.le, hxSource.2.le⟩ (lt_of_not_ge hn)
      rw [← htau a, ← htau x, hxy] at hlt
      exact (not_lt_of_ge hy.2) hlt
  obtain ⟨hxpos, hxformula⟩ := hcenter x hxCenter
  have hyformula : y = x / sqrt (1 + k * x ^ 2) := hxy.symm.trans hxformula
  have hsqrtpos : 0 < sqrt (1 + k * x ^ 2) := sqrt_pos.mpr hxpos
  have hsqrtsq := sq_sqrt hxpos.le
  have hinv : 1 - k * y ^ 2 = (1 + k * x ^ 2)⁻¹ := by
    rw [hyformula]
    field_simp
    nlinarith
  refine ⟨hinv ▸ inv_pos.mpr hxpos, ?_⟩
  change x = y / sqrt (1 - k * y ^ 2)
  rw [hinv, sqrt_inv, hyformula]
  rw [div_inv_eq_mul, div_mul_cancel₀ _ hsqrtpos.ne']

end Real
