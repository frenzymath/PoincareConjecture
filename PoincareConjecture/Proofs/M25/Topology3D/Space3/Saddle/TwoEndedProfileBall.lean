import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.BallNeighborhood
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SmoothOpenChart
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Convert
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false

open Set Metric Filter Function
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 3000000 in

theorem exists_two_ended_profile_ball
    (P : SurgeryCapProfile) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (ell top lambdaMinus lambdaPlus : ℝ)
    (horder : ell < top) (hminus : 0 < lambdaMinus)
    (hplus : 0 < lambdaPlus) :
    let M := flatCapDiffeomorph P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
    let lower := (fun q : UnitTwoSphere =>
      T ((P.model q).1, ell + lambdaMinus * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let upper := (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambdaPlus * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    ∃ (nu : ℝ)
      (g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞)
      (Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
      (B : BallNeighborhoodChart E3 E3),
      0 < nu ∧ nu < 1 / 8 ∧
      nu * (lambdaMinus + lambdaPlus + 1) < (top - ell) / 8 ∧
      (∀ z : ℝ,
        g z =
          (1 - Real.smoothTransition ((z + nu) / (2 * nu))) *
            (ell + lambdaMinus * z) +
          Real.smoothTransition ((z + nu) / (2 * nu)) *
            (top + lambdaPlus * z)) ∧
      (∀ z : ℝ, 0 < deriv (fun t : ℝ => g t) z) ∧
      (∀ z : ℝ, z ≤ -nu → g z = ell + lambdaMinus * z) ∧
      (∀ z : ℝ, nu ≤ z → g z = top + lambdaPlus * z) ∧
      (∀ y : E3, Q y =
        ((M (heightCoordinates y)).1, g ((M (heightCoordinates y)).2))) ∧
      (∀ p : E2 × ℝ, Q.symm p = heightCoordinates.symm (M.symm (p.1, g.symm p.2))) ∧
      B.chart = Q.toHomeomorph.toOpenPartialHomeomorph.trans T ∧
      B.chart.source = Q ⁻¹' T.source ∧ B.chart.target = T.target ∧
      (∀ y : E3, B.chart y = T (Q y)) ∧
      (∀ y : E3, B.chart.symm y = Q.symm (T.symm y)) ∧
      B.inside = T '' (Q '' ball (0 : E3) 1) ∧
      B.closedRegion = T '' (Q '' closedBall (0 : E3) 1) ∧
      B.boundary = lower ∪
        T '' (sphere (0 : E2) 1 ×ˢ Icc ell top) ∪ upper ∧
      (∀ z ∈ Icc ell top,
        B.inside ∩ {y : E3 | H y = z} = T '' (ball (0 : E2) 1 ×ˢ ({z} : Set ℝ)) ∧
        B.closedRegion ∩ {y : E3 | H y = z} =
          T '' (closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ))) ∧
      B.closedRegion ⊆ {y : E3 |
        ell - lambdaMinus * P.heightBound ≤ H y ∧
        H y ≤ top + lambdaPlus * P.heightBound} := by
  classical
  let M := flatCapDiffeomorph P.horizontal P.vertical
    P.horizontal_smooth P.vertical_smooth
    (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let J := heightCoordinates.toDiffeomorph.trans M
  have hJq (q : UnitTwoSphere) : J (q : E3) = P.model q := rfl
  have hJmem (A : Set E3) (p : E2 × ℝ) : p ∈ J '' A ↔ J.symm p ∈ A := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [J.symm_apply_apply] using hy
    · intro hp
      exact ⟨J.symm p, hp, J.apply_symm_apply p⟩
  have hJhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 := by
    apply flatCapDiffeomorph_fst_norm_le P.horizontal P.vertical
      P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne')
      P.horizontal_pos P.horizontal_bound
    change ‖(heightCoordinates y).1‖ ^ 2 + (heightCoordinates y).2 ^ 2 ≤ 1
    rw [← heightCoordinates_norm_sq]
    nlinarith [mem_closedBall_zero_iff.mp hy, norm_nonneg y]
  have hsq (r : ℝ) (hr : 0 ≤ r) :
      (r < 1 ↔ r ^ 2 < 1) ∧ (r ≤ 1 ↔ r ^ 2 ≤ 1) ∧ (r = 1 ↔ r ^ 2 = 1) := by
    refine ⟨?_, ?_, ?_⟩ <;> constructor <;> intro h <;> nlinarith
  obtain ⟨m, hm, hmb⟩ := (isCompact_closedBall (0 : E2) 1).exists_forall_le'
    P.vertical_smooth.continuous.continuousOn (fun x _ => P.vertical_pos x)
  have hb : 0 < min (1 / 8 : ℝ)
      (min (m / 8) ((top - ell) / (8 * (lambdaMinus + lambdaPlus + 1)))) := by
    apply lt_min (by norm_num)
    exact lt_min (by positivity) (div_pos (sub_pos.mpr horder) (by positivity))
  obtain ⟨nu, hnu, hnub⟩ := exists_between hb
  have hnu1 : nu < 1 / 8 := lt_of_lt_of_le hnub (min_le_left _ _)
  have hnum : nu < m / 8 :=
    lt_of_lt_of_le (lt_of_lt_of_le hnub (min_le_right _ _)) (min_le_left _ _)
  have hnuquot : nu < (top - ell) / (8 * (lambdaMinus + lambdaPlus + 1)) :=
    lt_of_lt_of_le (lt_of_lt_of_le hnub (min_le_right _ _)) (min_le_right _ _)
  have hgap : nu * (lambdaMinus + lambdaPlus + 1) < (top - ell) / 8 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 8 * (lambdaMinus + lambdaPlus + 1))).mp hnuquot
    nlinarith
  have hsmall (x : E2) (z : ℝ) (hz : |z| ≤ nu) :
      ((x, z) ∈ J '' ball (0 : E3) 1 ↔ ‖x‖ < 1) ∧
      ((x, z) ∈ J '' closedBall (0 : E3) 1 ↔ ‖x‖ ≤ 1) ∧
      ((x, z) ∈ J '' sphere (0 : E3) 1 ↔ ‖x‖ = 1) := by
    by_cases hx : ‖x‖ ≤ 1
    · let v := z / P.vertical x
      have hv : |v| < 1 / 4 := by
        dsimp [v]
        rw [abs_div, abs_of_pos (P.vertical_pos x)]
        apply (div_lt_iff₀ (P.vertical_pos x)).mpr
        nlinarith [hmb x (mem_closedBall_zero_iff.mpr hx)]
      have hvp : 0 < 1 - v ^ 2 := by nlinarith [sq_abs v, abs_nonneg v]
      have hvi : (P.vertical x)⁻¹ * z = v := by dsimp [v]; ring
      have hinv : J.symm (x, z) =
          heightCoordinates.symm (Real.sqrt (1 - v ^ 2) • x, v) := by
        change heightCoordinates.symm
          ((P.horizontal ((P.vertical x)⁻¹ * z))⁻¹ • x, (P.vertical x)⁻¹ * z) = _
        rw [hvi, P.horizontal_near v hv.le, inv_inv]
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
  have hJclosed : IsCompact (J '' closedBall (0 : E3) 1) :=
    (isCompact_closedBall (0 : E3) 1).image J.continuous
  have hJopen : IsOpen (J '' ball (0 : E3) 1) := J.toHomeomorph.isOpenMap _ isOpen_ball
  have hJnonempty : (J '' closedBall (0 : E3) 1).Nonempty :=
    ⟨J 0, 0, by simp, rfl⟩
  have hext (sigma : ℝ) (hsigma : |sigma| = 1) :
      ∀ p ∈ J '' closedBall (0 : E3) 1, sigma * p.2 ≤ P.heightBound := by
    obtain ⟨p, hp, hmax⟩ := hJclosed.exists_isMaxOn hJnonempty
      (f := fun p : E2 × ℝ => sigma * p.2) (by fun_prop)
    obtain ⟨y, hy, rfl⟩ := hp
    have hyb : y ∈ sphere (0 : E3) 1 := by
      by_contra hyb
      have hyn : ‖y‖ ≤ 1 := mem_closedBall_zero_iff.mp hy
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
      have h : sigma * p'.2 ≤ sigma * (J y).2 := hmax hp'
      rw [hstep] at h
      linarith
    have hbnd : |(J y).2| ≤ P.heightBound := P.height_bound ⟨y, hyb⟩
    have hsign : sigma * (J y).2 ≤ |(J y).2| := by
      calc
        _ ≤ |sigma * (J y).2| := le_abs_self _
        _ = _ := by rw [abs_mul, hsigma, one_mul]
    exact fun p hp => (hmax hp).trans (hsign.trans hbnd)
  have hJheight (p : E2 × ℝ) (hp : p ∈ J '' closedBall (0 : E3) 1) :
      -P.heightBound ≤ p.2 ∧ p.2 ≤ P.heightBound := by
    have hl := hext (-1) (by norm_num) p hp
    have hu := hext 1 (by norm_num) p hp
    constructor <;> linarith
  let chi : ℝ → ℝ := fun z => Real.smoothTransition ((z + nu) / (2 * nu))
  have hchi : ContDiff ℝ ∞ chi := Real.smoothTransition.contDiff.comp (by fun_prop)
  have hchir (z : ℝ) : chi z ∈ Icc (0 : ℝ) 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hchim : Monotone chi := by
    intro x y hxy
    exact Real.smoothTransition.monotone
      (div_le_div_of_nonneg_right (by linarith only [hxy] : x + nu ≤ y + nu) (by positivity))
  have hchiz (z : ℝ) (hz : z ≤ -nu) : chi z = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have hchio (z : ℝ) (hz : nu ≤ z) : chi z = 1 := by
    apply Real.smoothTransition.one_of_one_le
    apply (le_div_iff₀ (by positivity : 0 < 2 * nu)).mpr
    linarith
  let f : ℝ → ℝ := fun z =>
    (1 - chi z) * (ell + lambdaMinus * z) + chi z * (top + lambdaPlus * z)
  have hf : ContDiff ℝ ∞ f :=
    ((contDiff_const.sub hchi).mul (contDiff_const.add (contDiff_const.mul contDiff_id))).add
      (hchi.mul (contDiff_const.add (contDiff_const.mul contDiff_id)))
  have hleft (z : ℝ) (hz : z ≤ -nu) : f z = ell + lambdaMinus * z := by
    simp only [f, hchiz z hz, sub_zero, one_mul, zero_mul, add_zero]
  have hright (z : ℝ) (hz : nu ≤ z) : f z = top + lambdaPlus * z := by
    simp only [f, hchio z hz, sub_self, zero_mul, one_mul, zero_add]
  have hfd (z : ℝ) : HasDerivAt f
      ((1 - chi z) * lambdaMinus + chi z * lambdaPlus +
        deriv chi z * (top - ell + (lambdaPlus - lambdaMinus) * z)) z := by
    have hd := ((hchi.differentiable (by simp)) z).hasDerivAt
    convert! ((hd.const_sub 1).mul
      (((hasDerivAt_id z).const_mul lambdaMinus).const_add ell)).add
      (hd.mul (((hasDerivAt_id z).const_mul lambdaPlus).const_add top)) using 1
    simp only [id_eq]
    ring
  have hfpos (z : ℝ) : 0 < deriv f z := by
    by_cases hz : z < -nu
    · have heq : f =ᶠ[𝓝 z] fun w => ell + lambdaMinus * w := by
        filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
        exact hleft w hw.le
      have hd := (((hasDerivAt_id z).const_mul lambdaMinus).const_add ell).congr_of_eventuallyEq heq
      simpa only [hd.deriv, mul_one] using hminus
    by_cases hz' : nu < z
    · have heq : f =ᶠ[𝓝 z] fun w => top + lambdaPlus * w := by
        filter_upwards [isOpen_Ioi.mem_nhds hz'] with w hw
        exact hright w hw.le
      have hd := (((hasDerivAt_id z).const_mul lambdaPlus).const_add top).congr_of_eventuallyEq heq
      simpa only [hd.deriv, mul_one] using hplus
    have hzl : -nu ≤ z := le_of_not_gt hz
    have hzu : z ≤ nu := le_of_not_gt hz'
    have hdif : 0 < top - ell + (lambdaPlus - lambdaMinus) * z := by
      have hl := mul_le_mul_of_nonneg_left hzl hplus.le
      have hu := mul_le_mul_of_nonneg_left hzu hminus.le
      nlinarith
    have hconv : 0 < (1 - chi z) * lambdaMinus + chi z * lambdaPlus := by
      by_cases ht : chi z = 1
      · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using hplus
      · have ht' : chi z < 1 := lt_of_le_of_ne (hchir z).2 ht
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht') hminus)
          (mul_nonneg (hchir z).1 hplus.le)
    rw [(hfd z).deriv]
    exact add_pos_of_pos_of_nonneg hconv (mul_nonneg hchim.deriv_nonneg hdif.le)
  have hfm : StrictMono f := strictMono_of_deriv_pos hfpos
  have hfs : Surjective f := by
    intro w
    let a := min (-nu) ((w - ell) / lambdaMinus)
    let b := max nu ((w - top) / lambdaPlus)
    have ha : a ≤ -nu := min_le_left _ _
    have hb' : nu ≤ b := le_max_left _ _
    have hab : a ≤ b := by linarith
    have hlo : f a ≤ w := by
      rw [hleft a ha]
      have h := mul_le_mul_of_nonneg_left
        (min_le_right (-nu) ((w - ell) / lambdaMinus)) hminus.le
      have heq : lambdaMinus * ((w - ell) / lambdaMinus) = w - ell := by field_simp [hminus.ne']
      rw [heq] at h
      change lambdaMinus * a ≤ w - ell at h
      linarith
    have hhi : w ≤ f b := by
      rw [hright b hb']
      have h := mul_le_mul_of_nonneg_left
        (le_max_right nu ((w - top) / lambdaPlus)) hplus.le
      have heq : lambdaPlus * ((w - top) / lambdaPlus) = w - top := by field_simp [hplus.ne']
      rw [heq] at h
      change w - top ≤ lambdaPlus * b at h
      linarith
    obtain ⟨z, _, hz⟩ := intermediate_value_Icc hab hf.continuous.continuousOn ⟨hlo, hhi⟩
    exact ⟨z, hz⟩
  have hfdiff : ∀ z ∈ (univ : Set ℝ), ∃ A : ℝ ≃L[ℝ] ℝ,
      HasFDerivAt f (A : ℝ →L[ℝ] ℝ) z := by
    intro z _
    let L : ℝ →L[ℝ] ℝ := ContinuousLinearMap.toSpanSingleton ℝ (deriv f z)
    have hLi : Injective L := by
      apply (injective_iff_map_eq_zero L).mpr
      intro x hx
      change x * deriv f z = 0 at hx
      exact (mul_eq_zero.mp hx).resolve_right (hfpos z).ne'
    have hLs : Surjective L := by
      intro y
      refine ⟨y / deriv f z, ?_⟩
      change y / deriv f z * deriv f z = y
      exact div_mul_cancel₀ _ (hfpos z).ne'
    obtain ⟨A, hA⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr ⟨hLi, hLs⟩
    refine ⟨ContinuousLinearEquiv.ofUnit A, ?_⟩
    change HasFDerivAt f (A : ℝ →L[ℝ] ℝ) z
    rw [hA]
    exact (((hf.differentiable (by simp)) z).hasDerivAt).hasFDerivAt
  let e := smoothOpenChart f isOpen_univ hf.contDiffOn hfdiff hfm.injective.injOn
  have het : e.target = univ := by
    change f '' univ = univ
    exact image_univ_of_surjective hfs
  have hei : ContDiff ℝ ∞ e.symm := by
    apply contDiffOn_univ.mp
    rw [← het]
    exact smoothOpenChart_symm_contDiffOn f isOpen_univ hf.contDiffOn hfdiff hfm.injective.injOn
  let g : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞ := {
    toEquiv := {
      toFun := e
      invFun := e.symm
      left_inv := fun z => e.left_inv (mem_univ z)
      right_inv := fun z => e.right_inv (by rw [het]; exact mem_univ z) }
    contMDiff_toFun := hf.contMDiff
    contMDiff_invFun := hei.contMDiff }
  have hgm : StrictMono (fun z : ℝ => g z) := hfm
  have hgleft (z : ℝ) (hz : z ≤ -nu) : g z = ell + lambdaMinus * z := hleft z hz
  have hgright (z : ℝ) (hz : nu ≤ z) : g z = top + lambdaPlus * z := hright z hz
  have hgl : g (-nu) = ell - lambdaMinus * nu := by rw [hgleft _ le_rfl]; ring
  have hgu : g nu = top + lambdaPlus * nu := hgright _ le_rfl
  have hinvrange (z : ℝ) (hl : g (-nu) ≤ z) (hu : z ≤ g nu) : |g.symm z| ≤ nu := by
    apply abs_le.mpr
    constructor
    · apply hgm.le_iff_le.mp
      simpa only [g.apply_symm_apply] using hl
    · apply hgm.le_iff_le.mp
      simpa only [g.apply_symm_apply] using hu
  have hinvcut (z : ℝ) (hz : z ∈ Icc ell top) : |g.symm z| < nu := by
    apply abs_lt.mpr
    constructor
    · apply hgm.lt_iff_lt.mp
      rw [g.apply_symm_apply, hgl]
      nlinarith [hz.1]
    · apply hgm.lt_iff_lt.mp
      rw [g.apply_symm_apply, hgu]
      nlinarith [hz.2]
  let A : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ := {
    toEquiv := (Equiv.refl E2).prodCongr g.toEquiv
    contMDiff_toFun := (contDiff_fst.prodMk (g.contDiff.comp contDiff_snd)).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk (g.symm.contDiff.comp contDiff_snd)).contMDiff }
  let Q := J.trans A
  have hQ (y : E3) : Q y = ((J y).1, g (J y).2) := rfl
  have hQi (p : E2 × ℝ) : Q.symm p = J.symm (p.1, g.symm p.2) := rfl
  have hQmem (V : Set E3) (p : E2 × ℝ) :
      p ∈ Q '' V ↔ (p.1, g.symm p.2) ∈ J '' V := by
    rw [hJmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change J.symm ((J y).1, g.symm (g (J y).2)) ∈ V
      simpa only [g.symm_apply_apply, Prod.eta, J.symm_apply_apply] using hy
    · intro hp
      exact ⟨Q.symm p, hp, Q.apply_symm_apply p⟩
  let S0 := J '' sphere (0 : E3) 1
  let L0 := (fun p : E2 × ℝ => (p.1, ell + lambdaMinus * p.2)) ''
    (S0 ∩ {p : E2 × ℝ | p.2 ≤ 0})
  let U0 := (fun p : E2 × ℝ => (p.1, top + lambdaPlus * p.2)) ''
    (S0 ∩ {p : E2 × ℝ | 0 ≤ p.2})
  have hSphere : Q '' sphere (0 : E3) 1 =
      L0 ∪ (sphere (0 : E2) 1 ×ˢ Icc ell top) ∪ U0 := by
    apply Subset.antisymm
    · rintro ⟨x, z⟩ hp
      have hp' := (hQmem (sphere (0 : E3) 1) (x, z)).mp hp
      by_cases hl : g.symm z ≤ -nu
      · left; left
        refine ⟨(x, g.symm z), ⟨hp', ?_⟩, Prod.ext rfl ?_⟩
        · change g.symm z ≤ 0
          linarith only [hl, hnu]
        have heq := g.apply_symm_apply z
        rwa [hgleft _ hl] at heq
      by_cases hu : nu ≤ g.symm z
      · right
        refine ⟨(x, g.symm z), ⟨hp', ?_⟩, Prod.ext rfl ?_⟩
        · change 0 ≤ g.symm z
          linarith only [hu, hnu]
        have heq := g.apply_symm_apply z
        rwa [hgright _ hu] at heq
      have hrange : -nu ≤ g.symm z ∧ g.symm z ≤ nu :=
        ⟨(lt_of_not_ge hl).le, (lt_of_not_ge hu).le⟩
      have hx : ‖x‖ = 1 := (hsmall x (g.symm z) (abs_le.mpr hrange)).2.2.mp hp'
      have hzlo : ell - lambdaMinus * nu ≤ z := by
        have h := hgm.monotone hrange.1
        simpa only [g.apply_symm_apply, hgl] using h
      have hzhi : z ≤ top + lambdaPlus * nu := by
        have h := hgm.monotone hrange.2
        simpa only [g.apply_symm_apply, hgu] using h
      by_cases hzlow : z ≤ ell
      · left; left
        have hvlo : -nu ≤ (z - ell) / lambdaMinus :=
          (le_div_iff₀ hminus).mpr (by nlinarith)
        have hvhi : (z - ell) / lambdaMinus ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzlow) hminus.le
        refine ⟨(x, (z - ell) / lambdaMinus),
          ⟨(hsmall x _ (abs_le.mpr ⟨hvlo, hvhi.trans hnu.le⟩)).2.2.mpr hx, hvhi⟩,
          Prod.ext rfl ?_⟩
        dsimp
        field_simp [hminus.ne']
        ring
      by_cases hzhigh : top ≤ z
      · right
        have hvlo : 0 ≤ (z - top) / lambdaPlus :=
          div_nonneg (sub_nonneg.mpr hzhigh) hplus.le
        have hvhi : (z - top) / lambdaPlus ≤ nu :=
          (div_le_iff₀ hplus).mpr (by nlinarith)
        refine ⟨(x, (z - top) / lambdaPlus),
          ⟨(hsmall x _ (abs_le.mpr ⟨(neg_nonpos.mpr hnu.le).trans hvlo, hvhi⟩)).2.2.mpr hx,
            hvlo⟩, Prod.ext rfl ?_⟩
        dsimp
        field_simp [hplus.ne']
        ring
      exact Or.inl (Or.inr ⟨mem_sphere_zero_iff_norm.mpr hx,
        ⟨(lt_of_not_ge hzlow).le, (lt_of_not_ge hzhigh).le⟩⟩)
    · intro p hp
      rcases hp with (hp | hp) | hp
      · rcases hp with ⟨⟨x, v⟩, ⟨hv, hv0⟩, rfl⟩
        apply (hQmem _ _).mpr
        by_cases hl : v ≤ -nu
        · have heq : g.symm (ell + lambdaMinus * v) = v := by
            apply g.toEquiv.injective
            change g (g.symm (ell + lambdaMinus * v)) = g v
            rw [g.apply_symm_apply, hgleft v hl]
          simpa only [heq] using hv
        · have hvn : |v| ≤ nu := abs_le.mpr ⟨(lt_of_not_ge hl).le, hv0.trans hnu.le⟩
          have hx := (hsmall x v hvn).2.2.mp hv
          have hnew := hinvrange (ell + lambdaMinus * v)
            (by rw [hgl]; nlinarith [mul_pos hminus (sub_pos.mpr (lt_of_not_ge hl))])
            (by rw [hgu]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hminus.le hv0])
          exact (hsmall x _ hnew).2.2.mpr hx
      · rcases p with ⟨x, z⟩
        exact (hQmem _ _).mpr ((hsmall x _ (hinvcut z hp.2).le).2.2.mpr
          (mem_sphere_zero_iff_norm.mp hp.1))
      · rcases hp with ⟨⟨x, v⟩, ⟨hv, hv0⟩, rfl⟩
        apply (hQmem _ _).mpr
        by_cases hu : nu ≤ v
        · have heq : g.symm (top + lambdaPlus * v) = v := by
            apply g.toEquiv.injective
            change g (g.symm (top + lambdaPlus * v)) = g v
            rw [g.apply_symm_apply, hgright v hu]
          simpa only [heq] using hv
        · have hvn : |v| ≤ nu :=
            abs_le.mpr ⟨(neg_nonpos.mpr hnu.le).trans hv0, (lt_of_not_ge hu).le⟩
          have hx := (hsmall x v hvn).2.2.mp hv
          have hnew := hinvrange (top + lambdaPlus * v)
            (by rw [hgl]; nlinarith [mul_nonneg hplus.le hv0])
            (by rw [hgu]; nlinarith [mul_pos hplus (sub_pos.mpr (lt_of_not_ge hu))])
          exact (hsmall x _ hnew).2.2.mpr hx
  have hsouth (q : UnitTwoSphere) : (P.model q).2 ≤ 0 ↔ (heightCoordinates (q : E3)).2 ≤ 0 :=
    surgeryCapModel_snd_nonpos_iff P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
      (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne') P.vertical_pos q
  have hnorth (q : UnitTwoSphere) : 0 ≤ (P.model q).2 ↔ 0 ≤ (heightCoordinates (q : E3)).2 := by
    simpa only [not_lt, SurgeryCapProfile.model] using not_congr
      (surgeryCapModel_snd_neg_iff P.horizontal P.vertical P.horizontal_smooth P.vertical_smooth
        (fun z => (P.horizontal_pos z).ne') (fun x => (P.vertical_pos x).ne') P.vertical_pos q)
  have hlower : T '' L0 = (fun q : UnitTwoSphere =>
      T ((P.model q).1, ell + lambdaMinus * (P.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    apply Subset.antisymm
    · rintro _ ⟨p, ⟨v, ⟨⟨y, hy, rfl⟩, hv⟩, rfl⟩, rfl⟩
      exact ⟨⟨y, hy⟩, (hsouth ⟨y, hy⟩).mp hv, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨_, ⟨P.model q, ⟨⟨q, q.property, hJq q⟩, (hsouth q).mpr hq⟩, rfl⟩, rfl⟩
  have hupper : T '' U0 = (fun q : UnitTwoSphere =>
      T ((P.model q).1, top + lambdaPlus * (P.model q).2)) ''
        {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2} := by
    apply Subset.antisymm
    · rintro _ ⟨p, ⟨v, ⟨⟨y, hy, rfl⟩, hv⟩, rfl⟩, rfl⟩
      exact ⟨⟨y, hy⟩, (hnorth ⟨y, hy⟩).mp hv, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨_, ⟨P.model q, ⟨⟨q, q.property, hJq q⟩, (hnorth q).mpr hq⟩, rfl⟩, rfl⟩
  have hQsource : Q '' closedBall (0 : E3) 1 ⊆ T.source := by
    rintro p ⟨y, hy, rfl⟩
    exact hsource ⟨mem_closedBall_zero_iff.mpr (hJhor y hy), mem_univ _⟩
  let B : BallNeighborhoodChart E3 E3 := {
    chart := Q.toHomeomorph.toOpenPartialHomeomorph.trans T
    closedBall_subset_source := fun y hy => ⟨mem_univ y, hQsource ⟨y, hy, rfl⟩⟩
    smooth := hT.comp Q.contDiff.contDiffOn (fun _ hp => hp.2)
    smooth_symm := Q.symm.contDiff.comp_contDiffOn (hTi.mono inter_subset_left) }
  have hBsource : B.chart.source = Q ⁻¹' T.source := by
    ext y
    change (y ∈ (univ : Set E3) ∧ Q y ∈ T.source) ↔ Q y ∈ T.source
    simp only [mem_univ, true_and]
  have hBtarget : B.chart.target = T.target := by
    ext y
    change (y ∈ T.target ∧ T.symm y ∈ (univ : Set (E2 × ℝ))) ↔ y ∈ T.target
    simp only [mem_univ, and_true]
  have hBinside : B.inside = T '' (Q '' ball (0 : E3) 1) := by
    change (T ∘ Q) '' ball (0 : E3) 1 = _
    exact image_comp _ _ _
  have hBclosed : B.closedRegion = T '' (Q '' closedBall (0 : E3) 1) := by
    change (T ∘ Q) '' closedBall (0 : E3) 1 = _
    exact image_comp _ _ _
  have hBboundary : B.boundary = T '' L0 ∪
      T '' (sphere (0 : E2) 1 ×ˢ Icc ell top) ∪ T '' U0 := by
    change (T ∘ Q) '' sphere (0 : E3) 1 = _
    rw [image_comp, hSphere, image_union, image_union]
  have hQcut (z : ℝ) (hz : z ∈ Icc ell top) :
      (Q '' ball (0 : E3) 1) ∩ {p : E2 × ℝ | p.2 = z} = ball (0 : E2) 1 ×ˢ ({z} : Set ℝ) ∧
      (Q '' closedBall (0 : E3) 1) ∩ {p : E2 × ℝ | p.2 = z} =
        closedBall (0 : E2) 1 ×ˢ ({z} : Set ℝ) := by
    have ho (x : E2) : (x, z) ∈ Q '' ball (0 : E3) 1 ↔ ‖x‖ < 1 :=
      (hQmem _ _).trans (hsmall x _ (hinvcut z hz).le).1
    have hc (x : E2) : (x, z) ∈ Q '' closedBall (0 : E3) 1 ↔ ‖x‖ ≤ 1 :=
      (hQmem _ _).trans (hsmall x _ (hinvcut z hz).le).2.1
    constructor
    · ext p
      rcases p with ⟨x, w⟩
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨mem_ball_zero_iff.mpr ((ho x).mp hp), rfl⟩
      · rintro ⟨hx, rfl⟩
        exact ⟨(ho x).mpr (mem_ball_zero_iff.mp hx), rfl⟩
    · ext p
      rcases p with ⟨x, w⟩
      constructor
      · rintro ⟨hp, rfl⟩
        exact ⟨mem_closedBall_zero_iff.mpr ((hc x).mp hp), rfl⟩
      · rintro ⟨hx, rfl⟩
        exact ⟨(hc x).mpr (mem_closedBall_zero_iff.mp hx), rfl⟩
  have hTcut (V : Set (E2 × ℝ)) (hV : V ⊆ T.source) (z : ℝ) :
      (T '' V) ∩ {y : E3 | H y = z} = T '' (V ∩ {p : E2 × ℝ | p.2 = z}) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨p, hp, rfl⟩, hz⟩
      have hh : H (T p) = p.2 := hheight p (hV hp)
      exact ⟨p, ⟨hp, hh.symm.trans hz⟩, rfl⟩
    · rintro _ ⟨p, ⟨hp, hz⟩, rfl⟩
      have hh : H (T p) = p.2 := hheight p (hV hp)
      exact ⟨⟨p, hp, rfl⟩, hh.trans hz⟩
  refine ⟨nu, g, Q, B, hnu, hnu1, hgap, fun _ => rfl, hfpos, hgleft, hgright,
    hQ, hQi, rfl, hBsource, hBtarget, fun _ => rfl, fun _ => rfl,
    hBinside, hBclosed, ?_, ?_, ?_⟩
  · rw [hlower, hupper] at hBboundary
    exact hBboundary
  · intro z hz
    constructor
    · rw [hBinside, hTcut _ ((image_mono ball_subset_closedBall).trans hQsource), (hQcut z hz).1]
    · rw [hBclosed, hTcut _ hQsource, (hQcut z hz).2]
  · rw [hBclosed]
    rintro y ⟨p, ⟨v, hv, rfl⟩, rfl⟩
    have hh : H (T (Q v)) = g (J v).2 := hheight (Q v) (hQsource ⟨v, hv, rfl⟩)
    have hvb := hJheight (J v) ⟨v, hv, rfl⟩
    have hbnu : nu ≤ P.heightBound := by linarith [P.one_le_heightBound]
    have hlo := hgm.monotone hvb.1
    have hhi := hgm.monotone hvb.2
    rw [hgleft (-P.heightBound) (by linarith)] at hlo
    rw [hgright P.heightBound hbnu] at hhi
    change ell - lambdaMinus * P.heightBound ≤ H (T (Q v)) ∧
      H (T (Q v)) ≤ top + lambdaPlus * P.heightBound
    rw [hh]
    constructor <;> nlinarith

end PoincareConjecture.M25.Topology3D
