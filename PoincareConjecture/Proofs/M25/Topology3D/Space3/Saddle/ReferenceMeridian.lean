import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ReferenceRadialCorrection
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_nonnested_reference_meridian
    (sigma : ℝ) (hsigma : 0 < sigma) (hsigmaSmall : sigma ≤ 1 / 16)
    (d : ℝ → ℝ) (hd : ContDiff ℝ ∞ d)
    (hdNear : ∀ q : ℝ, 0 ≤ q → q ≤ sigma / 2 →
      d q = Real.sqrt (1 - q) - 1 + q / 2)
    (hdZero : ∀ q : ℝ, sigma ≤ q → d q = 0)
    (hdBounds : ∀ q : ℝ, 0 ≤ q → -q ^ 2 / 2 ≤ d q ∧ d q ≤ 0)
    (hdDeriv : ∀ q : ℝ, 0 ≤ q → |deriv d q| ≤ 1 / 16) :
    let K : ℝ → ℝ := fun w => w ^ 2 + w + d (1 - w ^ 2)
    ∃ (e ell : ℝ) (L : OpenPartialHomeomorph ℝ ℝ),
      0 < e ∧ e < 1 / 16 ∧ ell < -1 / 2 ∧
      L.source = Ioo (-1 - e) (1 / 4) ∧
      L.target = Ioo ell (3 / 4) ∧
      ContDiffOn ℝ ∞ L L.source ∧
      ContDiffOn ℝ ∞ L.symm L.target ∧
      StrictMonoOn L L.source ∧
      (∀ w ∈ L.source, 0 < deriv L w) ∧
      (∀ w : ℝ, L w =
        if w < -1 / 2 then -Real.sqrt (K w + 1 / 4)
        else Real.sqrt (K w + 1 / 4)) ∧
      ell = L (-1 - e) ∧
      L (-1) = -1 / 2 ∧ L (-1 / 2) = 0 ∧ L 0 = 1 / 2 ∧
      (∀ w ∈ Icc (-3 / 4) (1 / 8), L w = w + 1 / 2) ∧
      (∀ w ∈ L.source, (L w) ^ 2 = K w + 1 / 4) := by
  classical
  let K : ℝ → ℝ := fun w => w ^ 2 + w + d (1 - w ^ 2)
  let R : ℝ → ℝ := fun w => K w + 1 / 4
  let k1 : ℝ → ℝ := fun w => 2 * w + 1 - 2 * w * deriv d (1 - w ^ 2)
  let f : ℝ → ℝ := fun w =>
    if w < -1 / 2 then -Real.sqrt (R w) else Real.sqrt (R w)
  have hK : ContDiff ℝ ∞ K := ((contDiff_id.pow 2).add contDiff_id).add
    (hd.comp ((contDiff_const (c := (1 : ℝ))).sub (contDiff_id.pow 2)))
  have hR : ContDiff ℝ ∞ R := hK.add (contDiff_const (c := (1 / 4 : ℝ)))
  have hKd (w : ℝ) : HasDerivAt K (k1 w) w := by
    have hp : HasDerivAt (fun z : ℝ => z ^ 2) (2 * w) w := by
      simpa using hasDerivAt_pow 2 w
    have hcomp := ((hd.differentiable (by simp) (1 - w ^ 2)).hasDerivAt).comp w
      (hp.const_sub 1)
    exact ((hp.add (hasDerivAt_id w)).add hcomp).congr_deriv (by dsimp only [k1]; ring)
  have hRd (w : ℝ) : HasDerivAt R (k1 w) w := (hKd w).add_const (1 / 4)
  have hk1 : Continuous k1 := by
    have heq : k1 = deriv K := funext fun w => (hKd w).deriv.symm
    rw [heq]
    exact hK.continuous_deriv (by simp)
  let V : Set ℝ := Ioo (-7 / 8) (3 / 8)
  have hZero (w : ℝ) (hw : w ∈ V) : d (1 - w ^ 2) = 0 := by
    apply hdZero
    have hprod : 0 < (w + 7 / 8) * (7 / 8 - w) :=
      mul_pos (by linarith [hw.1]) (by linarith [hw.2])
    nlinarith
  have hRaff (w : ℝ) (hw : w ∈ V) : R w = (w + 1 / 2) ^ 2 := by
    dsimp only [R, K]
    rw [hZero w hw]
    ring
  have hfaff (w : ℝ) (hw : w ∈ V) : f w = w + 1 / 2 := by
    dsimp only [f]
    rw [hRaff w hw, Real.sqrt_sq_eq_abs]
    split_ifs with h
    · rw [abs_of_neg (by linarith)]
      ring
    · rw [abs_of_nonneg (by linarith)]
  have hAffineLocal (w : ℝ) (hw : w ∈ V) :
      ContDiffAt ℝ ∞ f w ∧ 0 < deriv f w := by
    have heq : f =ᶠ[𝓝 w] (fun z : ℝ => z + 1 / 2) := by
      filter_upwards [isOpen_Ioo.mem_nhds hw] with z hz
      exact hfaff z hz
    have hdf : HasDerivAt f 1 w :=
      ((hasDerivAt_id w).add_const (1 / 2)).congr_of_eventuallyEq heq
    have ha : ContDiffAt ℝ ∞ (fun z : ℝ => z + 1 / 2) w :=
      (contDiff_id.add contDiff_const).contDiffAt
    refine ⟨ha.congr_of_eventuallyEq heq, ?_⟩
    rw [hdf.deriv]
    norm_num
  have hLeft (w : ℝ) (hw : w ∈ Icc (-1 : ℝ) (-3 / 4)) :
      0 < R w ∧ k1 w < 0 := by
    have hq0 : 0 ≤ 1 - w ^ 2 := by
      have hh : 0 ≤ (w + 1) * (1 - w) :=
        mul_nonneg (by linarith [hw.1]) (by linarith [hw.2])
      nlinarith
    have hwsq : (1 / 16 : ℝ) ≤ (w + 1 / 2) ^ 2 := by
      nlinarith [hw.2, sq_nonneg (w + 3 / 4)]
    have habw : |w| ≤ 1 := abs_le.mpr ⟨hw.1, by linarith [hw.2]⟩
    have habd := hdDeriv (1 - w ^ 2) hq0
    have hcor : |2 * w * deriv d (1 - w ^ 2)| ≤ 1 / 8 := by
      rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
      calc
        2 * |w| * |deriv d (1 - w ^ 2)| ≤ 2 * 1 * (1 / 16) :=
          mul_le_mul (mul_le_mul_of_nonneg_left habw (by norm_num)) habd
            (abs_nonneg _) (by norm_num)
        _ = 1 / 8 := by ring
    have hkneg : k1 w < 0 := by
      have hh := (abs_le.mp hcor).1
      dsimp only [k1]
      linarith [hw.2]
    refine ⟨?_, hkneg⟩
    have hReq : R w = (w + 1 / 2) ^ 2 + d (1 - w ^ 2) := by dsimp [R, K]; ring
    rw [hReq]
    by_cases hq : sigma ≤ 1 - w ^ 2
    · rw [hdZero _ hq]
      linarith
    · have hqsmall : 1 - w ^ 2 ≤ 1 / 16 := (lt_of_not_ge hq).le.trans hsigmaSmall
      have hqsq : (1 - w ^ 2) ^ 2 ≤ (1 / 16 : ℝ) ^ 2 :=
        (sq_le_sq₀ hq0 (by norm_num)).mpr hqsmall
      have hlow := (hdBounds (1 - w ^ 2) hq0).1
      nlinarith
  have hNegativeLocal (w : ℝ) (hw : w < -1 / 2) (hRw : 0 < R w)
      (hkw : k1 w < 0) : ContDiffAt ℝ ∞ f w ∧ 0 < deriv f w := by
    have heq : f =ᶠ[𝓝 w] (fun z : ℝ => -Real.sqrt (R z)) := by
      filter_upwards [isOpen_Iio.mem_nhds hw] with z hz
      exact if_pos hz
    have hdf : HasDerivAt f (-(k1 w / (2 * Real.sqrt (R w)))) w :=
      (((hRd w).sqrt hRw.ne').neg).congr_of_eventuallyEq heq
    refine ⟨((hR.contDiffAt.sqrt hRw.ne').neg).congr_of_eventuallyEq heq, ?_⟩
    rw [hdf.deriv]
    exact neg_pos.mpr (div_neg_of_neg_of_pos hkw
      (mul_pos (by norm_num) (Real.sqrt_pos.mpr hRw)))
  have hd0 : d 0 = 0 := by
    have hh := hdNear 0 (by norm_num) (by linarith)
    norm_num at hh
    exact hh
  have hfMinus : f (-1) = -1 / 2 := by
    have hRm : R (-1) = 1 / 4 := by dsimp [R, K]; norm_num [hd0]
    dsimp only [f]
    rw [if_pos (by norm_num : (-1 : ℝ) < -1 / 2), hRm]
    norm_num
  let W : Set ℝ := {w | w < -3 / 4 ∧ 0 < R w ∧ k1 w < 0}
  have hW : IsOpen W := (isOpen_lt continuous_id continuous_const).inter
    ((isOpen_lt continuous_const hR.continuous).inter (isOpen_lt hk1 continuous_const))
  have hWm : (-1 : ℝ) ∈ W :=
    ⟨by norm_num, hLeft (-1) ⟨le_rfl, by norm_num⟩⟩
  obtain ⟨delta, hdelta, hdeltaW⟩ := Metric.mem_nhds_iff.mp (hW.mem_nhds hWm)
  let e := min (delta / 2) (1 / 32)
  have he : 0 < e := lt_min (half_pos hdelta) (by norm_num)
  have heSmall : e < 1 / 16 := (min_le_right _ _).trans_lt (by norm_num)
  have heDelta : e < delta := (min_le_left _ _).trans_lt (half_lt_self hdelta)
  let a : ℝ := -1 - e
  let C : Set ℝ := Icc a (1 / 4)
  let U : Set ℝ := Ioo a (1 / 4)
  have hExtend (w : ℝ) (hw : w ∈ Icc a (-1)) : w ∈ W := by
    apply hdeltaW
    rw [mem_ball, Real.dist_eq, abs_of_nonpos (by linarith [hw.2])]
    dsimp only [a] at hw
    linarith [hw.1]
  have hAll (w : ℝ) (hw : w ∈ C) :
      ContDiffAt ℝ ∞ f w ∧ 0 < deriv f w ∧ 0 ≤ R w := by
    by_cases hlo : w ≤ -3 / 4
    · have hleft : 0 < R w ∧ k1 w < 0 := by
        by_cases hm : w ≤ -1
        · exact (hExtend w ⟨hw.1, hm⟩).2
        · exact hLeft w ⟨(lt_of_not_ge hm).le, hlo⟩
      have hh := hNegativeLocal w (by linarith) hleft.1 hleft.2
      exact ⟨hh.1, hh.2, hleft.1.le⟩
    · have hwV : w ∈ V := ⟨by linarith, by linarith [hw.2]⟩
      have hh := hAffineLocal w hwV
      exact ⟨hh.1, hh.2, (hRaff w hwV).symm ▸ sq_nonneg (w + 1 / 2)⟩
  have hCcont : ContinuousOn f C :=
    fun w hw => (hAll w hw).1.continuousAt.continuousWithinAt
  have hCmono : StrictMonoOn f C :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) hCcont
      (fun w hw => (hAll w (interior_subset hw)).2.1)
  have hUdiff : ContDiffOn ℝ ∞ f U :=
    fun w hw => (hAll w (Ioo_subset_Icc_self hw)).1.contDiffWithinAt
  have hUpos (w : ℝ) (hw : w ∈ U) : 0 < deriv f w :=
    (hAll w (Ioo_subset_Icc_self hw)).2.1
  have hab : a < 1 / 4 := by dsimp only [a]; linarith
  let ell := f a
  have hell : ell < -1 / 2 := by
    have hh := hCmono (left_mem_Icc.mpr hab.le)
      (show (-1 : ℝ) ∈ C from ⟨by dsimp only [a]; linarith, by norm_num⟩)
      (show a < -1 by dsimp only [a]; linarith)
    exact hfMinus ▸ hh
  have hfQuarter : f (1 / 4) = 3 / 4 := by
    rw [hfaff (1 / 4) ⟨by norm_num, by norm_num⟩]
    norm_num
  have hImage : f '' U = Ioo ell (3 / 4) := by
    have hh := hCcont.image_Ioo_of_strictMonoOn hab.le hCmono
    rw [hfQuarter] at hh
    exact hh
  have hfdiff : ∀ w ∈ U, ∃ A : ℝ ≃L[ℝ] ℝ,
      HasFDerivAt f (A : ℝ →L[ℝ] ℝ) w := by
    intro w hw
    let T : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (deriv f w)
    have hp := hUpos w hw
    have hTi : Injective T := by
      apply (injective_iff_map_eq_zero T).mpr
      intro s hs
      change s * deriv f w = 0 at hs
      exact (mul_eq_zero.mp hs).resolve_right hp.ne'
    have hTs : Surjective T := by
      intro s
      refine ⟨s / deriv f w, ?_⟩
      change s / deriv f w * deriv f w = s
      exact div_mul_cancel₀ _ hp.ne'
    obtain ⟨A, hA⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hTi, hTs⟩
    refine ⟨ContinuousLinearEquiv.ofUnit A, ?_⟩
    change HasFDerivAt f (A : ℝ →L[ℝ] ℝ) w
    rw [hA]
    exact ((hAll w (Ioo_subset_Icc_self hw)).1.differentiableAt (by simp)).hasDerivAt.hasFDerivAt
  have hi : InjOn f U := hCmono.injOn.mono Ioo_subset_Icc_self
  let L := smoothOpenChart f isOpen_Ioo hUdiff hfdiff hi
  have hLt : L.target = Ioo ell (3 / 4) := hImage
  have hLi : ContDiffOn ℝ ∞ L.symm L.target :=
    smoothOpenChart_symm_contDiffOn f isOpen_Ioo hUdiff hfdiff hi
  have hfHalf : f (-1 / 2) = 0 := by
    rw [hfaff (-1 / 2) ⟨by norm_num, by norm_num⟩]
    norm_num
  have hfZero : f 0 = 1 / 2 := by
    rw [hfaff 0 ⟨by norm_num, by norm_num⟩]
    norm_num
  refine ⟨e, ell, L, he, heSmall, hell, rfl, hLt, hUdiff, hLi,
    hCmono.mono Ioo_subset_Icc_self, hUpos, fun _ => rfl, rfl, hfMinus, hfHalf, hfZero, ?_, ?_⟩
  · intro w hw
    exact hfaff w ⟨by linarith [hw.1], by linarith [hw.2]⟩
  · intro w hw
    change f w ^ 2 = R w
    have hRw := (hAll w (Ioo_subset_Icc_self hw)).2.2
    dsimp only [f]
    split_ifs <;> simp only [neg_sq, Real.sq_sqrt hRw]

end PoincareConjecture.M25.Topology3D
