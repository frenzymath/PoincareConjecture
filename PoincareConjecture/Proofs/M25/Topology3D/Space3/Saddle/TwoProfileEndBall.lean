import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.TwoProfileNativeModel
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



theorem exists_two_profile_end_ball
    (Pm Pp : SurgeryCapProfile) (u : UnitTwoSphere)
    (T : OpenPartialHomeomorph (E2 × ℝ) E3)
    (hsource : closedBall (0 : E2) 1 ×ˢ (univ : Set ℝ) ⊆ T.source)
    (hT : ContDiffOn ℝ ∞ T T.source)
    (hTi : ContDiffOn ℝ ∞ T.symm T.target)
    (hheight : ∀ p ∈ T.source, ⟪(u : E3), T p⟫_ℝ = p.2)
    (ell top lm lp : ℝ) (horder : ell < top)
    (hlm : 0 < lm) (hlp : 0 < lp) :
    let H : E3 →L[ℝ] ℝ := InnerProductSpace.toDual ℝ E3 (u : E3)
    let lower := (fun q : UnitTwoSphere =>
      T ((Pm.model q).1, ell + lm * (Pm.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
    let north : E3 → E3 := fun y =>
      let p := flatCapDiffeomorph Pp.horizontal Pp.vertical
        Pp.horizontal_smooth Pp.vertical_smooth
        (fun z => (Pp.horizontal_pos z).ne')
        (fun x => (Pp.vertical_pos x).ne') (heightCoordinates y)
      T (p.1, top + lp * p.2)
    let upper := north '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2}
    ∃ (Q : Diffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E2 × ℝ) E3 (E2 × ℝ) ∞)
      (B : BallNeighborhoodChart E3 E3) (o : ℝ),
      0 < o ∧ o < 1 / 4 ∧
      B.chart = Q.toHomeomorph.toOpenPartialHomeomorph.trans T ∧
      B.chart.source = Q ⁻¹' T.source ∧ B.chart.target = T.target ∧
      (∀ y : E3, B.chart y = T (Q y)) ∧
      (∀ y : E3, B.chart.symm y = Q.symm (T.symm y)) ∧
      B.boundary = lower ∪ T '' (sphere (0 : E2) 1 ×ˢ Icc ell top) ∪ upper ∧
      B.inside ⊆ T '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) ∧
      B.closedRegion ⊆ T '' (closedBall (0 : E2) 1 ×ˢ
        Icc (ell - lm * Pm.heightBound) (top + lp * Pp.heightBound)) ∧
      (∀ z ∈ Icc ell top,
        B.inside ∩ {y : E3 | H y = z} = T '' (ball 0 1 ×ˢ ({z} : Set ℝ)) ∧
        B.closedRegion ∩ {y : E3 | H y = z} =
          T '' (closedBall 0 1 ×ˢ ({z} : Set ℝ))) ∧
      ∀ q : UnitTwoSphere, -o < (heightCoordinates (q : E3)).2 →
        north (q : E3) ∈ B.boundary := by
  classical
  let H := InnerProductSpace.toDual ℝ E3 (u : E3)
  let north : E3 → E3 := fun y =>
    let p := flatCapDiffeomorph Pp.horizontal Pp.vertical
      Pp.horizontal_smooth Pp.vertical_smooth
      (fun z => (Pp.horizontal_pos z).ne')
      (fun x => (Pp.vertical_pos x).ne') (heightCoordinates y)
    T (p.1, top + lp * p.2)
  have hnorthq (q : UnitTwoSphere) :
      north (q : E3) = T ((Pp.model q).1, top + lp * (Pp.model q).2) := rfl
  obtain ⟨eta, J, heta, heta1, hJhem, hJclosedBounds, hJstrict, hsmall0⟩ :=
    exists_two_profile_native_ball_model Pm Pp
  have hJm (q : UnitTwoSphere) := (hJhem q).1
  have hJp (q : UnitTwoSphere) := (hJhem q).2
  have hJhor (y : E3) (hy : y ∈ closedBall (0 : E3) 1) : ‖(J y).1‖ ≤ 1 :=
    (hJclosedBounds y hy).1
  have hJmem (S : Set E3) (p : E2 × ℝ) : p ∈ J '' S ↔ J.symm p ∈ S := by
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa only [J.symm_apply_apply] using hy
    · intro hp
      exact ⟨J.symm p, hp, J.apply_symm_apply p⟩
  have hb : 0 < min eta ((top - ell) / (8 * (lm + lp + 1))) :=
    lt_min heta (div_pos (sub_pos.mpr horder) (by positivity))
  obtain ⟨nu, hnu, hnub⟩ := exists_between hb
  have hnue : nu < eta := lt_of_lt_of_le hnub (min_le_left _ _)
  have hnu1 : nu < 1 / 8 := hnue.trans heta1
  have hgap : nu * (lm + lp + 1) < (top - ell) / 8 := by
    have hquot := lt_of_lt_of_le hnub (min_le_right _ _)
    have hh := (lt_div_iff₀ (by positivity : 0 < 8 * (lm + lp + 1))).mp hquot
    nlinarith
  have hsmall (x : E2) (z : ℝ) (hz : |z| ≤ nu) :
      ((x, z) ∈ J '' ball (0 : E3) 1 ↔ ‖x‖ < 1) ∧
      ((x, z) ∈ J '' closedBall (0 : E3) 1 ↔ ‖x‖ ≤ 1) ∧
      ((x, z) ∈ J '' sphere (0 : E3) 1 ↔ ‖x‖ = 1) :=
    hsmall0 x z (hz.trans hnue.le)
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
    (1 - chi z) * (ell + lm * z) + chi z * (top + lp * z)
  have hf : ContDiff ℝ ∞ f :=
    ((contDiff_const.sub hchi).mul (contDiff_const.add (contDiff_const.mul contDiff_id))).add
      (hchi.mul (contDiff_const.add (contDiff_const.mul contDiff_id)))
  have hleft (z : ℝ) (hz : z ≤ -nu) : f z = ell + lm * z := by
    simp only [f, hchiz z hz, sub_zero, one_mul, zero_mul, add_zero]
  have hright (z : ℝ) (hz : nu ≤ z) : f z = top + lp * z := by
    simp only [f, hchio z hz, sub_self, zero_mul, one_mul, zero_add]
  have hfd (z : ℝ) : HasDerivAt f
      ((1 - chi z) * lm + chi z * lp +
        deriv chi z * (top - ell + (lp - lm) * z)) z := by
    have hd := ((hchi.differentiable (by simp)) z).hasDerivAt
    convert! ((hd.const_sub 1).mul
      (((hasDerivAt_id z).const_mul lm).const_add ell)).add
      (hd.mul (((hasDerivAt_id z).const_mul lp).const_add top)) using 1
    simp only [id_eq]
    ring
  have hfpos (z : ℝ) : 0 < deriv f z := by
    by_cases hz : z < -nu
    · have heq : f =ᶠ[𝓝 z] fun w => ell + lm * w := by
        filter_upwards [isOpen_Iio.mem_nhds hz] with w hw
        exact hleft w hw.le
      have hd := (((hasDerivAt_id z).const_mul lm).const_add ell).congr_of_eventuallyEq heq
      simpa only [hd.deriv, mul_one] using hlm
    by_cases hz' : nu < z
    · have heq : f =ᶠ[𝓝 z] fun w => top + lp * w := by
        filter_upwards [isOpen_Ioi.mem_nhds hz'] with w hw
        exact hright w hw.le
      have hd := (((hasDerivAt_id z).const_mul lp).const_add top).congr_of_eventuallyEq heq
      simpa only [hd.deriv, mul_one] using hlp
    have hzl : -nu ≤ z := le_of_not_gt hz
    have hzu : z ≤ nu := le_of_not_gt hz'
    have hdif : 0 < top - ell + (lp - lm) * z := by
      have hl := mul_le_mul_of_nonneg_left hzl hlp.le
      have hu := mul_le_mul_of_nonneg_left hzu hlm.le
      nlinarith
    have hconv : 0 < (1 - chi z) * lm + chi z * lp := by
      by_cases ht : chi z = 1
      · simpa only [ht, sub_self, zero_mul, one_mul, zero_add] using hlp
      · have ht' : chi z < 1 := lt_of_le_of_ne (hchir z).2 ht
        exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr ht') hlm)
          (mul_nonneg (hchir z).1 hlp.le)
    rw [(hfd z).deriv]
    exact add_pos_of_pos_of_nonneg hconv (mul_nonneg hchim.deriv_nonneg hdif.le)
  have hfm : StrictMono f := strictMono_of_deriv_pos hfpos
  have hfs : Surjective f := by
    intro w
    let a := min (-nu) ((w - ell) / lm)
    let b := max nu ((w - top) / lp)
    have ha : a ≤ -nu := min_le_left _ _
    have hb' : nu ≤ b := le_max_left _ _
    have hab : a ≤ b := by linarith
    have hlo : f a ≤ w := by
      rw [hleft a ha]
      have h := mul_le_mul_of_nonneg_left (min_le_right (-nu) ((w - ell) / lm)) hlm.le
      have heq : lm * ((w - ell) / lm) = w - ell := by field_simp [hlm.ne']
      rw [heq] at h
      change lm * a ≤ w - ell at h
      linarith
    have hhi : w ≤ f b := by
      rw [hright b hb']
      have h := mul_le_mul_of_nonneg_left (le_max_right nu ((w - top) / lp)) hlp.le
      have heq : lp * ((w - top) / lp) = w - top := by field_simp [hlp.ne']
      rw [heq] at h
      change w - top ≤ lp * b at h
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
  have hgleft (z : ℝ) (hz : z ≤ -nu) : g z = ell + lm * z := hleft z hz
  have hgright (z : ℝ) (hz : nu ≤ z) : g z = top + lp * z := hright z hz
  have hgl : g (-nu) = ell - lm * nu := by rw [hgleft _ le_rfl]; ring
  have hgu : g nu = top + lp * nu := hgright _ le_rfl
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
  have hQmem (S : Set E3) (p : E2 × ℝ) :
      p ∈ Q '' S ↔ (p.1, g.symm p.2) ∈ J '' S := by
    rw [hJmem]
    constructor
    · rintro ⟨y, hy, rfl⟩
      change J.symm ((J y).1, g.symm (g (J y).2)) ∈ S
      simpa only [g.symm_apply_apply, Prod.eta, J.symm_apply_apply] using hy
    · intro hp
      exact ⟨Q.symm p, hp, Q.apply_symm_apply p⟩
  let S0 := J '' sphere (0 : E3) 1
  let L0 := (fun p : E2 × ℝ => (p.1, ell + lm * p.2)) ''
    (S0 ∩ {p : E2 × ℝ | p.2 ≤ 0})
  let U0 := (fun p : E2 × ℝ => (p.1, top + lp * p.2)) ''
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
      have hzlo : ell - lm * nu ≤ z := by
        have h := hgm.monotone hrange.1
        simpa only [g.apply_symm_apply, hgl] using h
      have hzhi : z ≤ top + lp * nu := by
        have h := hgm.monotone hrange.2
        simpa only [g.apply_symm_apply, hgu] using h
      by_cases hzlow : z ≤ ell
      · left; left
        have hvlo : -nu ≤ (z - ell) / lm := (le_div_iff₀ hlm).mpr (by nlinarith)
        have hvhi : (z - ell) / lm ≤ 0 :=
          div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hzlow) hlm.le
        refine ⟨(x, (z - ell) / lm),
          ⟨(hsmall x _ (abs_le.mpr ⟨hvlo, hvhi.trans hnu.le⟩)).2.2.mpr hx, hvhi⟩,
          Prod.ext rfl ?_⟩
        dsimp
        field_simp [hlm.ne']
        ring
      by_cases hzhigh : top ≤ z
      · right
        have hvlo : 0 ≤ (z - top) / lp := div_nonneg (sub_nonneg.mpr hzhigh) hlp.le
        have hvhi : (z - top) / lp ≤ nu := (div_le_iff₀ hlp).mpr (by nlinarith)
        refine ⟨(x, (z - top) / lp),
          ⟨(hsmall x _ (abs_le.mpr ⟨(neg_nonpos.mpr hnu.le).trans hvlo, hvhi⟩)).2.2.mpr hx,
            hvlo⟩, Prod.ext rfl ?_⟩
        dsimp
        field_simp [hlp.ne']
        ring
      exact Or.inl (Or.inr ⟨mem_sphere_zero_iff_norm.mpr hx,
        ⟨(lt_of_not_ge hzlow).le, (lt_of_not_ge hzhigh).le⟩⟩)
    · intro p hp
      rcases hp with (hp | hp) | hp
      · rcases hp with ⟨⟨x, v⟩, ⟨hv, hv0⟩, rfl⟩
        apply (hQmem _ _).mpr
        by_cases hl : v ≤ -nu
        · have heq : g.symm (ell + lm * v) = v := by
            apply g.toEquiv.injective
            change g (g.symm (ell + lm * v)) = g v
            rw [g.apply_symm_apply, hgleft v hl]
          simpa only [heq] using hv
        · have hvn : |v| ≤ nu := abs_le.mpr ⟨(lt_of_not_ge hl).le, hv0.trans hnu.le⟩
          have hx := (hsmall x v hvn).2.2.mp hv
          have hnew := hinvrange (ell + lm * v)
            (by rw [hgl]; nlinarith [mul_pos hlm (sub_pos.mpr (lt_of_not_ge hl))])
            (by rw [hgu]; nlinarith [mul_nonpos_of_nonneg_of_nonpos hlm.le hv0])
          exact (hsmall x _ hnew).2.2.mpr hx
      · rcases p with ⟨x, z⟩
        exact (hQmem _ _).mpr ((hsmall x _ (hinvcut z hp.2).le).2.2.mpr
          (mem_sphere_zero_iff_norm.mp hp.1))
      · rcases hp with ⟨⟨x, v⟩, ⟨hv, hv0⟩, rfl⟩
        apply (hQmem _ _).mpr
        by_cases hu : nu ≤ v
        · have heq : g.symm (top + lp * v) = v := by
            apply g.toEquiv.injective
            change g (g.symm (top + lp * v)) = g v
            rw [g.apply_symm_apply, hgright v hu]
          simpa only [heq] using hv
        · have hvn : |v| ≤ nu :=
            abs_le.mpr ⟨(neg_nonpos.mpr hnu.le).trans hv0, (lt_of_not_ge hu).le⟩
          have hx := (hsmall x v hvn).2.2.mp hv
          have hnew := hinvrange (top + lp * v)
            (by rw [hgl]; nlinarith [mul_nonneg hlp.le hv0])
            (by rw [hgu]; nlinarith [mul_pos hlp (sub_pos.mpr (lt_of_not_ge hu))])
          exact (hsmall x _ hnew).2.2.mpr hx
  have hsouth (q : UnitTwoSphere) :
      (J (q : E3)).2 ≤ 0 ↔ (heightCoordinates (q : E3)).2 ≤ 0 := by
    constructor
    · intro hq
      by_contra hn
      have hp := lt_of_not_ge hn
      rw [hJp q hp.le] at hq
      have hh := (surgeryCapModel_snd_pos_iff Pp.horizontal Pp.vertical
        Pp.horizontal_smooth Pp.vertical_smooth
        (fun z => (Pp.horizontal_pos z).ne') (fun x => (Pp.vertical_pos x).ne')
        Pp.vertical_pos q).mpr hp
      exact (not_lt_of_ge hq) hh
    · intro hq
      rw [hJm q hq]
      exact (surgeryCapModel_snd_nonpos_iff Pm.horizontal Pm.vertical
        Pm.horizontal_smooth Pm.vertical_smooth
        (fun z => (Pm.horizontal_pos z).ne') (fun x => (Pm.vertical_pos x).ne')
        Pm.vertical_pos q).mpr hq
  have hnorth (q : UnitTwoSphere) :
      0 ≤ (J (q : E3)).2 ↔ 0 ≤ (heightCoordinates (q : E3)).2 := by
    constructor
    · intro hq
      by_contra hn
      have hp := lt_of_not_ge hn
      rw [hJm q hp.le] at hq
      have hh := (surgeryCapModel_snd_neg_iff Pm.horizontal Pm.vertical
        Pm.horizontal_smooth Pm.vertical_smooth
        (fun z => (Pm.horizontal_pos z).ne') (fun x => (Pm.vertical_pos x).ne')
        Pm.vertical_pos q).mpr hp
      exact (not_lt_of_ge hq) hh
    · intro hq
      rw [hJp q hq]
      have hh := surgeryCapModel_snd_neg_iff Pp.horizontal Pp.vertical
        Pp.horizontal_smooth Pp.vertical_smooth
        (fun z => (Pp.horizontal_pos z).ne') (fun x => (Pp.vertical_pos x).ne')
        Pp.vertical_pos q
      exact le_of_not_gt (fun hp => (not_lt_of_ge hq) (hh.mp hp))
  have hlower : T '' L0 = (fun q : UnitTwoSphere =>
      T ((Pm.model q).1, ell + lm * (Pm.model q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} := by
    apply Subset.antisymm
    · rintro _ ⟨p, ⟨v, ⟨⟨y, hy, rfl⟩, hv⟩, rfl⟩, rfl⟩
      have hq := (hsouth ⟨y, hy⟩).mp hv
      refine ⟨⟨y, hy⟩, hq, ?_⟩
      exact congrArg (fun p : E2 × ℝ => T (p.1, ell + lm * p.2))
        (hJm ⟨y, hy⟩ hq).symm
    · rintro _ ⟨q, hq, rfl⟩
      refine ⟨_, ⟨J (q : E3), ⟨⟨q, q.property, rfl⟩, (hsouth q).mpr hq⟩, rfl⟩, ?_⟩
      rw [hJm q hq]
  have hupper : T '' U0 =
      north '' {y : E3 | ‖y‖ = 1 ∧ 0 ≤ (heightCoordinates y).2} := by
    apply Subset.antisymm
    · rintro _ ⟨p, ⟨v, ⟨⟨y, hy, rfl⟩, hv⟩, rfl⟩, rfl⟩
      have hq := (hnorth ⟨y, hy⟩).mp hv
      refine ⟨y, ⟨mem_sphere_zero_iff_norm.mp hy, hq⟩, ?_⟩
      change north ((⟨y, hy⟩ : UnitTwoSphere) : E3) = _
      rw [hnorthq, ← hJp ⟨y, hy⟩ hq]
    · rintro _ ⟨y, ⟨hy, hq⟩, rfl⟩
      let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
      refine ⟨_, ⟨J y, ⟨⟨y, q.property, rfl⟩, (hnorth q).mpr hq⟩, rfl⟩, ?_⟩
      change T ((J (q : E3)).1, top + lp * (J (q : E3)).2) = north (q : E3)
      rw [hnorthq, hJp q hq]
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
  have hTcut (S : Set (E2 × ℝ)) (hS : S ⊆ T.source) (z : ℝ) :
      (T '' S) ∩ {y : E3 | H y = z} = T '' (S ∩ {p : E2 × ℝ | p.2 = z}) := by
    apply Subset.antisymm
    · rintro _ ⟨⟨p, hp, rfl⟩, hz⟩
      have hh : H (T p) = p.2 := hheight p (hS hp)
      exact ⟨p, ⟨hp, hh.symm.trans hz⟩, rfl⟩
    · rintro _ ⟨p, ⟨hp, hz⟩, rfl⟩
      have hh : H (T p) = p.2 := hheight p (hS hp)
      exact ⟨⟨p, hp, rfl⟩, hh.trans hz⟩
  have hinside : B.inside ⊆ T '' (ball (0 : E2) 1 ×ˢ (univ : Set ℝ)) := by
    rw [hBinside]
    rintro y ⟨p, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨Q v, ⟨mem_ball_zero_iff.mpr (hJstrict v hv), mem_univ _⟩, rfl⟩
  have hclosed : B.closedRegion ⊆ T '' (closedBall (0 : E2) 1 ×ˢ
      Icc (ell - lm * Pm.heightBound) (top + lp * Pp.heightBound)) := by
    rw [hBclosed]
    rintro y ⟨p, ⟨v, hv, rfl⟩, rfl⟩
    have hvb := (hJclosedBounds v hv).2
    have hlo := hgm.monotone hvb.1
    have hhi := hgm.monotone hvb.2
    rw [hgleft (-Pm.heightBound) (by linarith [Pm.one_le_heightBound])] at hlo
    rw [hgright Pp.heightBound (by linarith [Pp.one_le_heightBound])] at hhi
    refine ⟨Q v, ⟨mem_closedBall_zero_iff.mpr (hJhor v hv), ?_, ?_⟩, rfl⟩
    · change ell - lm * Pm.heightBound ≤ g (J v).2
      nlinarith
    · change g (J v).2 ≤ top + lp * Pp.heightBound
      exact hhi
  let o := min (1 / 8 : ℝ) ((top - ell) / (4 * lp))
  have ho : 0 < o := lt_min (by norm_num) (div_pos (sub_pos.mpr horder) (by positivity))
  have ho1 : o < 1 / 4 := (min_le_left _ _).trans_lt (by norm_num)
  have hogap : lp * o ≤ (top - ell) / 4 := by
    have hh := mul_le_mul_of_nonneg_left
      (min_le_right (1 / 8 : ℝ) ((top - ell) / (4 * lp))) hlp.le
    have heq : lp * ((top - ell) / (4 * lp)) = (top - ell) / 4 := by field_simp [hlp.ne']
    rw [heq] at hh
    exact hh
  refine ⟨Q, B, o, ho, ho1, rfl, hBsource, hBtarget, fun _ => rfl, fun _ => rfl,
    ?_, hinside, hclosed, ?_, ?_⟩
  · rw [hlower, hupper] at hBboundary
    exact hBboundary
  · intro z hz
    constructor
    · rw [hBinside, hTcut _ ((image_mono ball_subset_closedBall).trans hQsource), (hQcut z hz).1]
    · rw [hBclosed, hTcut _ hQsource, (hQcut z hz).2]
  · intro q hq
    change north (q : E3) ∈ B.boundary
    by_cases hqpos : 0 ≤ (heightCoordinates (q : E3)).2
    · rw [hBboundary, hupper]
      exact Or.inr ⟨q, ⟨norm_eq_of_mem_sphere q, hqpos⟩, rfl⟩
    have hqneg : (heightCoordinates (q : E3)).2 < 0 := lt_of_not_ge hqpos
    have hqsmall : |(heightCoordinates (q : E3)).2| ≤ 1 / 4 := by
      apply abs_le.mpr
      constructor <;> linarith
    have hm := surgeryCapModel_cylinder Pp.horizontal Pp.vertical
      Pp.horizontal_smooth Pp.vertical_smooth
      (fun z => (Pp.horizontal_pos z).ne') (fun x => (Pp.vertical_pos x).ne')
      Pp.horizontal_near Pp.vertical_far q hqsmall
    change Pp.model q =
      ((circleDirection (heightCoordinates (q : E3)).1 : E2), (heightCoordinates (q : E3)).2) at hm
    rw [hBboundary, hnorthq, hm]
    apply Or.inl
    apply Or.inr
    refine ⟨((circleDirection (heightCoordinates (q : E3)).1 : E2),
      top + lp * (heightCoordinates (q : E3)).2), ⟨(circleDirection _).property, ?_, ?_⟩, rfl⟩
    · have hh := mul_lt_mul_of_pos_left hq hlp
      nlinarith
    · have hh := mul_nonpos_of_nonneg_of_nonpos hlp.le hqneg.le
      linarith

end PoincareConjecture.M25.Topology3D
