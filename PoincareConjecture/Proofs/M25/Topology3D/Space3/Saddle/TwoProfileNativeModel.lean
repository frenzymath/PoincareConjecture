import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Algebra.Module.Equiv
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring









set_option autoImplicit false

open Set Metric Filter Function MeasureTheory
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D



theorem exists_two_profile_native_ball_model
    (Pm Pp : SurgeryCapProfile) :
    ∃ (eta : ℝ)
      (J : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞),
      0 < eta ∧ eta < 1 / 8 ∧
      (∀ q : UnitTwoSphere,
        ((heightCoordinates (q : E3)).2 ≤ 0 → J (q : E3) = Pm.model q) ∧
        (0 ≤ (heightCoordinates (q : E3)).2 → J (q : E3) = Pp.model q)) ∧
      (∀ y ∈ closedBall (0 : E3) 1,
        ‖(J y).1‖ ≤ 1 ∧
        -Pm.heightBound ≤ (J y).2 ∧ (J y).2 ≤ Pp.heightBound) ∧
      (∀ y ∈ ball (0 : E3) 1, ‖(J y).1‖ < 1) ∧
      ∀ x : E2, ∀ z : ℝ, |z| ≤ eta →
        ((x, z) ∈ J '' ball (0 : E3) 1 ↔ ‖x‖ < 1) ∧
        ((x, z) ∈ J '' closedBall (0 : E3) 1 ↔ ‖x‖ ≤ 1) ∧
        ((x, z) ∈ J '' sphere (0 : E3) 1 ↔ ‖x‖ = 1) := by
  classical
  let d : ℝ := 1 / 8
  have hd : 0 < d := by norm_num [d]
  let s : ℝ → ℝ := fun z => Real.smoothTransition ((z + d) / (2 * d))
  have hs : ContDiff ℝ ∞ s := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hsr (z : ℝ) : s z ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hs0 (z : ℝ) (hz : z ≤ -d) : s z = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hs1 (z : ℝ) (hz : d ≤ z) : s z = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ (by positivity : 0 < 2 * d)).mpr
    linarith
  let chi : ℝ → ℝ := fun z => (s z + 1 - s (-z)) / 2
  have hchi : ContDiff ℝ ∞ chi :=
    ((hs.add contDiff_const).sub (hs.comp contDiff_neg)).div_const 2
  have hchir (z : ℝ) : chi z ∈ Icc (0 : ℝ) 1 := by
    dsimp [chi]
    constructor <;> linarith [(hsr z).1, (hsr z).2, (hsr (-z)).1, (hsr (-z)).2]
  have hchi0 (z : ℝ) (hz : z ≤ -d) : chi z = 0 := by
    simp only [chi, hs0 z hz, hs1 (-z) (by linarith), zero_add, sub_self, zero_div]
  have hchi1 (z : ℝ) (hz : d ≤ z) : chi z = 1 := by
    dsimp only [chi]
    rw [hs1 z hz, hs0 (-z) (by linarith)]
    norm_num
  have hchisym (z : ℝ) : chi z + chi (-z) = 1 := by
    dsimp [chi]
    rw [neg_neg]
    ring
  have hchii (a b : ℝ) : IntervalIntegrable chi volume a b :=
    hchi.continuous.intervalIntegrable a b
  have hchint : (∫ z in (-d)..d, chi z) = d := by
    have hn : (∫ z in (-d)..d, chi (-z)) = ∫ z in (-d)..d, chi z := by
      rw [intervalIntegral.integral_comp_neg, neg_neg]
    have hh : (∫ z in (-d)..d, chi z + chi (-z)) = 2 * d := by
      calc
        _ = ∫ z in (-d)..d, (1 : ℝ) :=
          intervalIntegral.integral_congr (fun z _ => hchisym z)
        _ = 2 * d := by simp only [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hneg : IntervalIntegrable (fun z : ℝ => chi (-z)) volume (-d) d :=
      (hchi.continuous.comp continuous_neg).intervalIntegrable (-d) d
    rw [intervalIntegral.integral_add (hchii (-d) d) hneg, hn] at hh
    linarith
  let A : ℝ → ℝ := fun z => ∫ t in (-d)..z, chi t
  have hAd (z : ℝ) : HasDerivAt A (chi z) z :=
    intervalIntegral.integral_hasDerivAt_right (hchii (-d) z)
      hchi.continuous.aestronglyMeasurable.stronglyMeasurableAtFilter
      hchi.continuous.continuousAt
  have hA : ContDiff ℝ ∞ A := by
    apply contDiff_infty_iff_deriv.mpr
    refine ⟨fun z => (hAd z).differentiableAt, ?_⟩
    have heq : deriv A = chi := funext fun z => (hAd z).deriv
    rw [heq]
    exact hchi
  have hA0 (z : ℝ) (hz : z ≤ -d) : A z = 0 := by
    change (∫ t in (-d)..z, chi t) = 0
    calc
      _ = ∫ t in (-d)..z, (0 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro t ht
        rw [uIcc_of_ge hz] at ht
        exact hchi0 t ht.2
      _ = 0 := by simp
  have hA1 (z : ℝ) (hz : d ≤ z) : A z = z := by
    have hi : (∫ t in d..z, chi t) = z - d := by
      calc
        _ = ∫ t in d..z, (1 : ℝ) := by
          apply intervalIntegral.integral_congr
          intro t ht
          rw [uIcc_of_le hz] at ht
          exact hchi1 t ht.1
        _ = z - d := by simp
    have hh := intervalIntegral.integral_add_adjacent_intervals (hchii (-d) d) (hchii d z)
    rw [hchint, hi] at hh
    change (∫ t in (-d)..z, chi t) = z
    linarith
  let a : ℝ → ℝ := fun z => (1 - s z) * Pm.horizontal z + s z * Pp.horizontal z
  have ha : ContDiff ℝ ∞ a :=
    ((contDiff_const.sub hs).mul Pm.horizontal_smooth).add (hs.mul Pp.horizontal_smooth)
  have hsame (z : ℝ) (hz : |z| ≤ 1 / 4) : Pm.horizontal z = Pp.horizontal z :=
    (Pm.horizontal_near z hz).trans (Pp.horizontal_near z hz).symm
  have ham (z : ℝ) (hz : z ≤ 0) : a z = Pm.horizontal z := by
    by_cases hzl : z ≤ -d
    · simp only [a, hs0 z hzl, sub_zero, one_mul, zero_mul, add_zero]
    have hzz : |z| ≤ 1 / 4 := by
      apply abs_le.mpr
      dsimp [d] at hzl
      constructor <;> linarith
    dsimp [a]
    rw [hsame z hzz]
    ring
  have hap (z : ℝ) (hz : 0 ≤ z) : a z = Pp.horizontal z := by
    by_cases hzr : d ≤ z
    · simp only [a, hs1 z hzr, sub_self, zero_mul, one_mul, zero_add]
    have hzz : |z| ≤ 1 / 4 := by
      apply abs_le.mpr
      dsimp [d] at hzr
      constructor <;> linarith
    dsimp [a]
    rw [hsame z hzz]
    ring
  have hapos (z : ℝ) : 0 < a z := by
    rcases le_total z 0 with hz | hz
    · rw [ham z hz]; exact Pm.horizontal_pos z
    · rw [hap z hz]; exact Pp.horizontal_pos z
  have hanear (z : ℝ) (hz : |z| ≤ 1 / 4) :
      a z = (Real.sqrt (1 - z ^ 2))⁻¹ := by
    rcases le_total z 0 with h | h
    · rw [ham z h]; exact Pm.horizontal_near z hz
    · rw [hap z h]; exact Pp.horizontal_near z hz
  have habound (z : ℝ) (hz : |z| < 1) : a z ≤ (Real.sqrt (1 - z ^ 2))⁻¹ := by
    rcases le_total z 0 with h | h
    · rw [ham z h]; exact Pm.horizontal_bound z hz
    · rw [hap z h]; exact Pp.horizontal_bound z hz
  let V : E2 × ℝ → ℝ := fun p =>
    Pm.vertical p.1 * (p.2 - A p.2) + Pp.vertical p.1 * A p.2
  have hV : ContDiff ℝ ∞ V :=
    ((Pm.vertical_smooth.comp contDiff_fst).mul
      (contDiff_snd.sub (hA.comp contDiff_snd))).add
      ((Pp.vertical_smooth.comp contDiff_fst).mul (hA.comp contDiff_snd))
  have hVd (x : E2) (z : ℝ) : HasDerivAt (fun t : ℝ => V (x, t))
      ((1 - chi z) * Pm.vertical x + chi z * Pp.vertical x) z := by
    change HasDerivAt (fun t : ℝ =>
      Pm.vertical x * (t - A t) + Pp.vertical x * A t) _ z
    convert! (((hasDerivAt_id z).sub (hAd z)).const_mul (Pm.vertical x)).add
      ((hAd z).const_mul (Pp.vertical x)) using 1
    ring
  have hVp (x : E2) (z : ℝ) :
      0 < (1 - chi z) * Pm.vertical x + chi z * Pp.vertical x := by
    by_cases h : chi z = 1
    · simpa only [h, sub_self, zero_mul, one_mul, zero_add] using Pp.vertical_pos x
    · have hlt : chi z < 1 := lt_of_le_of_ne (hchir z).2 h
      exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hlt) (Pm.vertical_pos x))
        (mul_nonneg (hchir z).1 (Pp.vertical_pos x).le)
  have hVm (x : E2) : StrictMono (fun z : ℝ => V (x, z)) := by
    apply strictMono_of_deriv_pos
    intro z
    rw [(hVd x z).deriv]
    exact hVp x z
  have hVl (x : E2) (z : ℝ) (hz : z ≤ -d) : V (x, z) = Pm.vertical x * z := by
    simp only [V, hA0 z hz, sub_zero, mul_zero, add_zero]
  have hVr (x : E2) (z : ℝ) (hz : d ≤ z) : V (x, z) = Pp.vertical x * z := by
    simp only [V, hA1 z hz, sub_self, mul_zero, zero_add]
  have hVs (x : E2) : Surjective (fun z : ℝ => V (x, z)) := by
    intro w
    let l := min (-d) (w / Pm.vertical x)
    let r := max d (w / Pp.vertical x)
    have hl : l ≤ -d := min_le_left _ _
    have hr : d ≤ r := le_max_left _ _
    have hlw : V (x, l) ≤ w := by
      rw [hVl x l hl]
      have hh := mul_le_mul_of_nonneg_left (min_le_right (-d) (w / Pm.vertical x))
        (Pm.vertical_pos x).le
      have heq : Pm.vertical x * (w / Pm.vertical x) = w := by
        field_simp [(Pm.vertical_pos x).ne']
      rw [heq] at hh
      exact hh
    have hwr : w ≤ V (x, r) := by
      rw [hVr x r hr]
      have hh := mul_le_mul_of_nonneg_left (le_max_right d (w / Pp.vertical x))
        (Pp.vertical_pos x).le
      have heq : Pp.vertical x * (w / Pp.vertical x) = w := by
        field_simp [(Pp.vertical_pos x).ne']
      rw [heq] at hh
      exact hh
    have hc : Continuous (fun z : ℝ => V (x, z)) :=
      hV.continuous.comp (continuous_const.prodMk continuous_id)
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc (by linarith : l ≤ r)
      hc.continuousOn ⟨hlw, hwr⟩
    exact ⟨z, hz⟩
  let B0 : E2 × ℝ → E2 × ℝ := fun p => (p.1, V p)
  have hB0 : ContDiff ℝ ∞ B0 := contDiff_fst.prodMk hV
  have hBi : Injective B0 := by
    rintro ⟨x, z⟩ ⟨y, w⟩ h
    have hxy : x = y := congrArg Prod.fst h
    subst y
    exact Prod.ext rfl ((hVm x).injective (congrArg Prod.snd h))
  have hBs : Surjective B0 := by
    rintro ⟨x, w⟩
    obtain ⟨z, hz⟩ := hVs x w
    exact ⟨(x, z), Prod.ext rfl hz⟩
  have hBD : ∀ p ∈ (univ : Set (E2 × ℝ)),
      ∃ L : (E2 × ℝ) ≃L[ℝ] (E2 × ℝ),
        HasFDerivAt B0 (L : E2 × ℝ →L[ℝ] E2 × ℝ) p := by
    intro p _
    let Dv := fderiv ℝ V p
    let k := (1 - chi p.2) * Pm.vertical p.1 + chi p.2 * Pp.vertical p.1
    have hk : 0 < k := hVp p.1 p.2
    have hDv : HasFDerivAt V Dv p := (hV.differentiable (by simp) p).hasFDerivAt
    let L0 : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ k
    have hL0i : Injective L0 := by
      apply (injective_iff_map_eq_zero L0).mpr
      intro t ht
      change t * k = 0 at ht
      exact (mul_eq_zero.mp ht).resolve_right hk.ne'
    have hL0s : Surjective L0 := by
      intro w
      exact ⟨w / k, div_mul_cancel₀ w hk.ne'⟩
    obtain ⟨unit, hunit⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hL0i, hL0s⟩
    let L1 := ContinuousLinearEquiv.ofUnit unit
    have hsp : Dv.comp (ContinuousLinearMap.inr ℝ E2 ℝ) = (L1 : ℝ →L[ℝ] ℝ) := by
      change Dv.comp (ContinuousLinearMap.inr ℝ E2 ℝ) = (unit : ℝ →L[ℝ] ℝ)
      rw [hunit]
      have hpair : HasFDerivAt (fun t : ℝ => (p.1, t))
          (ContinuousLinearMap.inr ℝ E2 ℝ) p.2 :=
        hasFDerivAt_prodMk_right p.1 p.2
      have hcomp : HasFDerivAt (fun t : ℝ => V (p.1, t))
          (Dv.comp (ContinuousLinearMap.inr ℝ E2 ℝ)) p.2 := by
        have hDv' : HasFDerivAt V Dv (p.1, p.2) := hDv
        exact HasFDerivAt.comp (f := fun t : ℝ => (p.1, t)) (g := V) p.2 hDv' hpair
      have hscalar : HasFDerivAt (fun t : ℝ => V (p.1, t)) L0 p.2 :=
        (hVd p.1 p.2).hasFDerivAt
      exact hcomp.unique hscalar
    let L := (ContinuousLinearEquiv.refl ℝ E2).skewProd L1
      (Dv.comp (ContinuousLinearMap.inl ℝ E2 ℝ))
    have hL : (L : E2 × ℝ →L[ℝ] E2 × ℝ) =
        (ContinuousLinearMap.fst ℝ E2 ℝ).prod Dv := by
      apply ContinuousLinearMap.ext
      intro v
      apply Prod.ext
      · rfl
      · change L1 v.2 + Dv (v.1, 0) = Dv v
        have hv : L1 v.2 = Dv (0, v.2) :=
          (congrArg (fun M : ℝ →L[ℝ] ℝ => M v.2) hsp).symm
        rw [hv, ← map_add]
        simp
    refine ⟨L, ?_⟩
    rw [hL]
    exact hasFDerivAt_fst.prodMk hDv
  let e := smoothOpenChart B0 isOpen_univ hB0.contDiffOn hBD hBi.injOn
  have het : e.target = univ := image_univ_of_surjective hBs
  have hei : ContDiff ℝ ∞ e.symm := by
    apply contDiffOn_univ.mp
    rw [← het]
    exact smoothOpenChart_symm_contDiffOn B0 isOpen_univ hB0.contDiffOn hBD hBi.injOn
  let B : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ := {
    toEquiv := {
      toFun := e
      invFun := e.symm
      left_inv := fun p => e.left_inv (mem_univ p)
      right_inv := fun p => e.right_inv (by rw [het]; exact mem_univ p) }
    contMDiff_toFun := hB0.contMDiff
    contMDiff_invFun := hei.contMDiff }
  have hBform (p : E2 × ℝ) : B p = (p.1, V p) := rfl
  let zeta : E2 × ℝ → ℝ := fun p => (B.symm p).2
  have hBifst (p : E2 × ℝ) : (B.symm p).1 = p.1 := by
    have hh := congrArg Prod.fst (B.apply_symm_apply p)
    simpa only [hBform] using hh
  have hzetav (p : E2 × ℝ) : V (p.1, zeta p) = p.2 := by
    have hh := congrArg Prod.snd (B.apply_symm_apply p)
    change V (B.symm p) = p.2 at hh
    have hp : (p.1, zeta p) = B.symm p := Prod.ext (hBifst p).symm rfl
    rw [hp]
    exact hh
  let C0 := flatCapDiffeomorph a (fun _ : E2 => (1 : ℝ)) ha contDiff_const
    (fun z => (hapos z).ne') (fun _ => one_ne_zero)
  let J := heightCoordinates.toDiffeomorph.trans (C0.trans B)
  have hJ (y : E3) : J y =
      (a (heightCoordinates y).2 • (heightCoordinates y).1,
        V (a (heightCoordinates y).2 • (heightCoordinates y).1, (heightCoordinates y).2)) := by
    change B (C0 (heightCoordinates y)) = _
    rw [hBform]
    simp only [C0, flatCapDiffeomorph_apply, one_mul]
  have hJi (p : E2 × ℝ) : J.symm p =
      heightCoordinates.symm ((a (zeta p))⁻¹ • p.1, zeta p) := by
    change heightCoordinates.symm (C0.symm (B.symm p)) = _
    simp only [C0, flatCapDiffeomorph_symm_apply, inv_one, one_mul, hBifst, zeta]
  have hJm (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      J (q : E3) = Pm.model q := by
    let x := (heightCoordinates (q : E3)).1
    let z := (heightCoordinates (q : E3)).2
    rw [hJ, ham z hq]
    change (Pm.horizontal z • x, V (Pm.horizontal z • x, z)) =
      (Pm.horizontal z • x, Pm.vertical (Pm.horizontal z • x) * z)
    refine Prod.ext rfl ?_
    by_cases hz : z ≤ -d
    · exact hVl _ z hz
    have hzz : |z| ≤ 1 / 4 := by
      apply abs_le.mpr
      dsimp [d] at hz
      constructor <;> linarith
    have hh := surgeryCapModel_cylinder Pm.horizontal Pm.vertical
      Pm.horizontal_smooth Pm.vertical_smooth
      (fun z => (Pm.horizontal_pos z).ne') (fun x => (Pm.vertical_pos x).ne')
      Pm.horizontal_near Pm.vertical_far q hzz
    have hX : ‖Pm.horizontal z • x‖ = 1 := by
      have hfirst := congrArg Prod.fst hh
      change Pm.horizontal z • x = (circleDirection x : E2) at hfirst
      rw [hfirst]
      exact norm_eq_of_mem_sphere (circleDirection x)
    have hbm := Pm.vertical_far (Pm.horizontal z • x) (by rw [hX]; norm_num)
    have hbp := Pp.vertical_far (Pm.horizontal z • x) (by rw [hX]; norm_num)
    simp only [V, hbm, hbp, one_mul]
    ring
  have hJp (q : UnitTwoSphere) (hq : 0 ≤ (heightCoordinates (q : E3)).2) :
      J (q : E3) = Pp.model q := by
    let x := (heightCoordinates (q : E3)).1
    let z := (heightCoordinates (q : E3)).2
    rw [hJ, hap z hq]
    change (Pp.horizontal z • x, V (Pp.horizontal z • x, z)) =
      (Pp.horizontal z • x, Pp.vertical (Pp.horizontal z • x) * z)
    refine Prod.ext rfl ?_
    by_cases hz : d ≤ z
    · exact hVr _ z hz
    have hzz : |z| ≤ 1 / 4 := by
      apply abs_le.mpr
      dsimp [d] at hz
      constructor <;> linarith
    have hh := surgeryCapModel_cylinder Pp.horizontal Pp.vertical
      Pp.horizontal_smooth Pp.vertical_smooth
      (fun z => (Pp.horizontal_pos z).ne') (fun x => (Pp.vertical_pos x).ne')
      Pp.horizontal_near Pp.vertical_far q hzz
    have hX : ‖Pp.horizontal z • x‖ = 1 := by
      have hfirst := congrArg Prod.fst hh
      change Pp.horizontal z • x = (circleDirection x : E2) at hfirst
      rw [hfirst]
      exact norm_eq_of_mem_sphere (circleDirection x)
    have hbm := Pm.vertical_far (Pp.horizontal z • x) (by rw [hX]; norm_num)
    have hbp := Pp.vertical_far (Pp.horizontal z • x) (by rw [hX]; norm_num)
    simp only [V, hbm, hbp, one_mul]
    ring
  have hJhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 := by
    have hh := flatCapDiffeomorph_fst_norm_le a (fun _ : E2 => (1 : ℝ)) ha contDiff_const
      (fun z => (hapos z).ne') (fun _ => one_ne_zero) hapos habound (heightCoordinates y)
      (by
        rw [← heightCoordinates_norm_sq]
        nlinarith [mem_closedBall_zero_iff.mp hy, norm_nonneg y])
    rw [hJ]
    exact hh
  have hJstrict (y : E3) (hy : y ∈ ball (0 : E3) 1) : ‖(J y).1‖ < 1 := by
    let x := (heightCoordinates y).1
    let z := (heightCoordinates y).2
    have hsq : ‖x‖ ^ 2 + z ^ 2 < 1 := by
      change ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 < 1
      rw [← heightCoordinates_norm_sq]
      nlinarith [mem_ball_zero_iff.mp hy, norm_nonneg y]
    have hz : |z| < 1 := by nlinarith [sq_abs z, abs_nonneg z, sq_nonneg ‖x‖]
    have hr : 0 < 1 - z ^ 2 := by nlinarith [sq_nonneg ‖x‖]
    have hxs : ‖x‖ < Real.sqrt (1 - z ^ 2) := by
      nlinarith [Real.sq_sqrt hr.le, Real.sqrt_nonneg (1 - z ^ 2), norm_nonneg x]
    rw [hJ, norm_smul, Real.norm_eq_abs, abs_of_pos (hapos z)]
    calc
      a z * ‖x‖ < a z * Real.sqrt (1 - z ^ 2) := mul_lt_mul_of_pos_left hxs (hapos z)
      _ ≤ (Real.sqrt (1 - z ^ 2))⁻¹ * Real.sqrt (1 - z ^ 2) :=
        mul_le_mul_of_nonneg_right (habound z hz) (Real.sqrt_nonneg _)
      _ = 1 := inv_mul_cancel₀ (Real.sqrt_pos.mpr hr).ne'
  have hboundary (q : UnitTwoSphere) :
      -Pm.heightBound ≤ (J (q : E3)).2 ∧ (J (q : E3)).2 ≤ Pp.heightBound := by
    rcases le_total (heightCoordinates (q : E3)).2 0 with hq | hq
    · rw [hJm q hq]
      have hb := abs_le.mp (Pm.height_bound q)
      have hn := (surgeryCapModel_snd_nonpos_iff Pm.horizontal Pm.vertical
        Pm.horizontal_smooth Pm.vertical_smooth
        (fun z => (Pm.horizontal_pos z).ne') (fun x => (Pm.vertical_pos x).ne')
        Pm.vertical_pos q).mpr hq
      exact ⟨hb.1, hn.trans (by linarith [Pp.one_le_heightBound])⟩
    · rw [hJp q hq]
      have hb := abs_le.mp (Pp.height_bound q)
      have hn : 0 ≤ (Pp.model q).2 := by
        have hh := surgeryCapModel_snd_neg_iff Pp.horizontal Pp.vertical
          Pp.horizontal_smooth Pp.vertical_smooth
          (fun z => (Pp.horizontal_pos z).ne') (fun x => (Pp.vertical_pos x).ne')
          Pp.vertical_pos q
        exact le_of_not_gt (fun hp => (not_lt_of_ge hq) (hh.mp hp))
      exact ⟨(by linarith [Pm.one_le_heightBound] : -Pm.heightBound ≤ 0).trans hn, hb.2⟩
  have hJclosed : IsCompact (J '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image J.continuous
  have hJopen : IsOpen (J '' ball (0 : E3) 1) := J.toHomeomorph.isOpenMap _ isOpen_ball
  have hJnonempty : (J '' closedBall (0 : E3) 1).Nonempty := ⟨J 0, 0, by simp, rfl⟩
  have hext (sigma M : ℝ) (hsigma : |sigma| = 1)
      (hb : ∀ q : UnitTwoSphere, sigma * (J (q : E3)).2 ≤ M) :
      ∀ p ∈ J '' closedBall (0 : E3) 1, sigma * p.2 ≤ M := by
    obtain ⟨p, hp, hmax⟩ := hJclosed.exists_isMaxOn hJnonempty
      (f := fun p : E2 × ℝ => sigma * p.2) (by fun_prop)
    obtain ⟨y, hy, rfl⟩ := hp
    have hyb : y ∈ sphere (0 : E3) 1 := by
      by_contra hyb
      have hyn := mem_closedBall_zero_iff.mp hy
      have hyl : ‖y‖ < 1 := lt_of_le_of_ne hyn (fun heq => hyb (mem_sphere_zero_iff_norm.mpr heq))
      obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hJopen (J y)
        ⟨y, mem_ball_zero_iff.mpr hyl, rfl⟩
      let p' : E2 × ℝ := ((J y).1, (J y).2 + sigma * (r / 2))
      have hp' : p' ∈ J '' closedBall (0 : E3) 1 := by
        apply image_mono ball_subset_closedBall
        apply hsub
        change dist ((J y).1, (J y).2 + sigma * (r / 2)) ((J y).1, (J y).2) < r
        rw [dist_prod_same_left, Real.dist_eq,
          show (J y).2 + sigma * (r / 2) - (J y).2 = sigma * (r / 2) by ring,
          abs_mul, hsigma, one_mul, abs_of_pos (by positivity : 0 < r / 2)]
        linarith
      have hsquare : sigma ^ 2 = 1 := by nlinarith [sq_abs sigma]
      have hstep : sigma * p'.2 = sigma * (J y).2 + r / 2 := by
        dsimp [p']
        calc
          _ = sigma * (J y).2 + sigma ^ 2 * (r / 2) := by ring
          _ = _ := by rw [hsquare, one_mul]
      have hh := hmax hp'
      change sigma * p'.2 ≤ sigma * (J y).2 at hh
      rw [hstep] at hh
      linarith
    exact fun p hp => (hmax hp).trans (hb ⟨y, hyb⟩)
  have hheight (y : E3) (hy : y ∈ closedBall (0 : E3) 1) :
      -Pm.heightBound ≤ (J y).2 ∧ (J y).2 ≤ Pp.heightBound := by
    have hl := hext (-1) Pm.heightBound (by norm_num)
      (fun q => by linarith [(hboundary q).1]) (J y) ⟨y, hy, rfl⟩
    have hu := hext 1 Pp.heightBound (by norm_num)
      (fun q => by simpa using (hboundary q).2) (J y) ⟨y, hy, rfl⟩
    constructor <;> linarith
  obtain ⟨mm, hmm, hmmb⟩ := (isCompact_closedBall (0 : E2) 1).exists_forall_le'
    Pm.vertical_smooth.continuous.continuousOn (fun x _ => Pm.vertical_pos x)
  obtain ⟨mp, hmp, hmpb⟩ := (isCompact_closedBall (0 : E2) 1).exists_forall_le'
    Pp.vertical_smooth.continuous.continuousOn (fun x _ => Pp.vertical_pos x)
  let m := min mm mp
  have hm : 0 < m := lt_min hmm hmp
  have hmb (x : E2) (hx : ‖x‖ ≤ 1) : m ≤ Pm.vertical x ∧ m ≤ Pp.vertical x :=
    ⟨(min_le_left _ _).trans (hmmb x (mem_closedBall_zero_iff.mpr hx)),
      (min_le_right _ _).trans (hmpb x (mem_closedBall_zero_iff.mpr hx))⟩
  let eta := min (1 / 16 : ℝ) (m / 32)
  have heta : 0 < eta := lt_min (by norm_num) (by positivity)
  have heta1 : eta < 1 / 8 := (min_le_left _ _).trans_lt (by norm_num)
  have hetam : eta < m / 16 := (min_le_right _ _).trans_lt (by linarith)
  have hJmem (S : Set E3) (p : E2 × ℝ) : p ∈ J '' S ↔ J.symm p ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [J.symm_apply_apply] using hy
    · intro hp
      exact ⟨J.symm p, hp, J.apply_symm_apply p⟩
  have hsq (r : ℝ) (hr : 0 ≤ r) :
      (r < 1 ↔ r ^ 2 < 1) ∧ (r ≤ 1 ↔ r ^ 2 ≤ 1) ∧ (r = 1 ↔ r ^ 2 = 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> nlinarith
  refine ⟨eta, J, heta, heta1, fun q => ⟨hJm q, hJp q⟩,
    fun y hy => ⟨hJhor y hy, hheight y hy⟩, hJstrict, ?_⟩
  intro x z hz
  by_cases hx : ‖x‖ ≤ 1
  · let v := zeta (x, z)
    have hvz : V (x, v) = z := hzetav (x, z)
    have hvl : -d < v := by
      apply (hVm x).lt_iff_lt.mp
      rw [hVl x (-d) le_rfl, hvz]
      have hl := (abs_le.mp hz).1
      have hb := (hmb x hx).1
      dsimp [d]
      nlinarith
    have hvr : v < d := by
      apply (hVm x).lt_iff_lt.mp
      rw [hVr x d le_rfl, hvz]
      have hu := (abs_le.mp hz).2
      have hb := (hmb x hx).2
      dsimp [d]
      nlinarith
    have hv : |v| < 1 / 4 := by
      apply abs_lt.mpr
      dsimp [d] at hvl hvr
      constructor <;> linarith
    have hvp : 0 < 1 - v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
    have hinv : J.symm (x, z) = heightCoordinates.symm (Real.sqrt (1 - v ^ 2) • x, v) := by
      rw [hJi, hanear v hv.le, inv_inv]
    have hnorm : ‖J.symm (x, z)‖ ^ 2 - 1 = (‖x‖ ^ 2 - 1) * (1 - v ^ 2) := by
      rw [hinv, heightCoordinates_symm_norm_sq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt hvp.le]
      ring
    have hlt : ‖J.symm (x, z)‖ ^ 2 < 1 ↔ ‖x‖ ^ 2 < 1 := by
      calc
        _ ↔ ‖J.symm (x, z)‖ ^ 2 - 1 < 0 := sub_lt_zero.symm
        _ ↔ (‖x‖ ^ 2 - 1) * (1 - v ^ 2) < 0 := by rw [hnorm]
        _ ↔ ‖x‖ ^ 2 - 1 < 0 := by
          simpa only [zero_mul] using (mul_lt_mul_iff_left₀ hvp
            (b := ‖x‖ ^ 2 - 1) (c := 0))
        _ ↔ ‖x‖ ^ 2 < 1 := sub_lt_zero
    have hle : ‖J.symm (x, z)‖ ^ 2 ≤ 1 ↔ ‖x‖ ^ 2 ≤ 1 := by
      calc
        _ ↔ ‖J.symm (x, z)‖ ^ 2 - 1 ≤ 0 := sub_nonpos.symm
        _ ↔ (‖x‖ ^ 2 - 1) * (1 - v ^ 2) ≤ 0 := by rw [hnorm]
        _ ↔ ‖x‖ ^ 2 - 1 ≤ 0 := by
          simpa only [zero_mul] using (mul_le_mul_iff_left₀ hvp
            (b := ‖x‖ ^ 2 - 1) (c := 0))
        _ ↔ ‖x‖ ^ 2 ≤ 1 := sub_nonpos
    have heq : ‖J.symm (x, z)‖ ^ 2 = 1 ↔ ‖x‖ ^ 2 = 1 := by
      constructor
      · intro hh
        have hh' : (‖x‖ ^ 2 - 1) * (1 - v ^ 2) = 0 := by rw [← hnorm, hh]; ring
        have := (mul_eq_zero.mp hh').resolve_right hvp.ne'
        linarith
      · intro hh
        rw [hh] at hnorm
        linarith
    simp only [hJmem, mem_ball_zero_iff, mem_closedBall_zero_iff, mem_sphere_zero_iff_norm]
    exact ⟨(hsq _ (norm_nonneg _)).1.trans (hlt.trans (hsq _ (norm_nonneg _)).1.symm),
      (hsq _ (norm_nonneg _)).2.1.trans (hle.trans (hsq _ (norm_nonneg _)).2.1.symm),
      (hsq _ (norm_nonneg _)).2.2.trans (heq.trans (hsq _ (norm_nonneg _)).2.2.symm)⟩
  · have hh : 1 < ‖x‖ := lt_of_not_ge hx
    have hc : (x, z) ∉ J '' closedBall (0 : E3) 1 := by
      rintro ⟨y, hy, heq⟩
      have h := hJhor y hy
      rw [heq] at h
      exact hx h
    exact ⟨iff_of_false (fun h => hc (image_mono ball_subset_closedBall h))
        (not_lt_of_ge hh.le), iff_of_false hc hx,
      iff_of_false (fun h => hc (image_mono sphere_subset_closedBall h)) (ne_of_gt hh)⟩

end PoincareConjecture.M25.Topology3D
