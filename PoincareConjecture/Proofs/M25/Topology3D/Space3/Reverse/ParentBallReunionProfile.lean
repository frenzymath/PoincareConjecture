import PoincareConjecture.Proofs.M25.Topology3D.Space3.Base.StackOfDiscsProfilePath
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryCapTag
import PoincareConjecture.Proofs.M25.Topology3D.Space3.SurgeryNeighborhood
import Mathlib.Analysis.Calculus.Deriv.Abs











set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D


noncomputable def reunionReflectedHorizontal (P : SurgeryCapProfile)
    (z : ℝ) : ℝ := P.horizontal |z|


theorem reunionReflectedHorizontal_spec (P : SurgeryCapProfile) :
    ContDiff ℝ ∞ (reunionReflectedHorizontal P) ∧
    (∀ z : ℝ, 0 < reunionReflectedHorizontal P z) ∧
    (∀ z : ℝ, |z| ≤ 1 / 4 → reunionReflectedHorizontal P z =
      (Real.sqrt (1 - z ^ 2))⁻¹) ∧
    (∀ z : ℝ, 1 / 2 ≤ |z| → reunionReflectedHorizontal P z = 1) ∧
    (∀ z : ℝ, |z| < 1 → reunionReflectedHorizontal P z ≤
      (Real.sqrt (1 - z ^ 2))⁻¹) ∧
    (∀ z : ℝ, 0 ≤ z → reunionReflectedHorizontal P z = P.horizontal z) ∧
    (∀ z : ℝ, z ≤ 0 → reunionReflectedHorizontal P z = P.horizontal (-z)) ∧
    ∀ z : ℝ, z ∉ Icc (-1 / 2 : ℝ) (-1 / 4) →
      reunionReflectedHorizontal P z = P.horizontal z := by
  have hnear (z : ℝ) (hz : |z| ≤ 1 / 4) :
      reunionReflectedHorizontal P z = (Real.sqrt (1 - z ^ 2))⁻¹ := by
    simpa only [reunionReflectedHorizontal, abs_abs, sq_abs] using
      P.horizontal_near |z| (by simpa only [abs_abs] using hz)
  have hfar (z : ℝ) (hz : 1 / 2 ≤ |z|) : reunionReflectedHorizontal P z = 1 := by
    exact P.horizontal_far |z| (by simpa only [abs_abs] using hz)
  have hsame (z : ℝ) (hz : |z| ≤ 1 / 4) :
      reunionReflectedHorizontal P z = P.horizontal z :=
    (hnear z hz).trans (P.horizontal_near z hz).symm
  have hs : ContDiff ℝ ∞ (reunionReflectedHorizontal P) := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z = 0
    · subst z
      apply P.horizontal_smooth.contDiffAt.congr_of_eventuallyEq
      filter_upwards [(isOpen_lt continuous_abs continuous_const).mem_nhds
        (show |(0 : ℝ)| < 1 / 4 by norm_num)] with x hx
      exact hsame x hx.le
    · exact P.horizontal_smooth.contDiffAt.comp z (contDiffAt_abs hz)
  refine ⟨hs, fun z => P.horizontal_pos |z|, hnear, hfar, ?_, ?_, ?_, ?_⟩
  · intro z hz
    simpa only [reunionReflectedHorizontal, abs_abs, sq_abs] using
      P.horizontal_bound |z| (by simpa only [abs_abs] using hz)
  · intro z hz
    simp only [reunionReflectedHorizontal, abs_of_nonneg hz]
  · intro z hz
    simp only [reunionReflectedHorizontal, abs_of_nonpos hz]
  · intro z hz
    by_cases hpos : 0 ≤ z
    · simp only [reunionReflectedHorizontal, abs_of_nonneg hpos]
    by_cases hsmall : |z| ≤ 1 / 4
    · exact hsame z hsmall
    have hlarge : 1 / 2 ≤ |z| := by
      by_contra h
      have hzneg : z < 0 := lt_of_not_ge hpos
      have habs : |z| = -z := abs_of_neg hzneg
      apply hz
      constructor <;> nlinarith only [lt_of_not_ge h, lt_of_not_ge hsmall, habs]
    rw [hfar z hlarge, P.horizontal_far z hlarge]


theorem reunion_reflected_model_spec (P : SurgeryCapProfile) :
    let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical
    let F := fun q : UnitTwoSphere => M 1 (heightCoordinates (q : E3))
    (∀ X : E2, ‖X‖ ≤ 1 → P.vertical X ≤ 2 * P.heightBound) ∧
    (∀ t : ℝ, ∀ q : UnitTwoSphere,
      ‖(M t (heightCoordinates (q : E3))).1‖ ≤ 1 ∧
      |(M t (heightCoordinates (q : E3))).2| ≤ 2 * P.heightBound) ∧
    (∀ t : ℝ, ∀ p : E2 × ℝ, p.2 ∉ Icc (-1 / 2 : ℝ) (-1 / 4) →
      M t p = M 0 p) ∧
    (∀ q : UnitTwoSphere, |(F q).2| ≤ P.heightBound) ∧
    F '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} =
      (fun p : E2 × ℝ => (p.1, -p.2)) ''
        (P.model '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}) ∧
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      (∀ q : UnitTwoSphere, |(F q).2| ≤ ε →
        |(heightCoordinates (q : E3)).2| < 1 / 4) ∧
      F '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0 ∧
        -ε ≤ (F q).2} = sphere (0 : E2) 1 ×ˢ Icc (-ε) 0 := by
  obtain ⟨hA, hApos, hAnear, _hAfar, hAbound, hAnorth, hAsouth, hAoff⟩ :=
    reunionReflectedHorizontal_spec P
  let M := stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
    P.vertical P.vertical
  let F := fun q : UnitTwoSphere => M 1 (heightCoordinates (q : E3))
  have hM (t : ℝ) (p : E2 × ℝ) :
      M t p = (stackProfileBlend P.horizontal (reunionReflectedHorizontal P) t p.2 • p.1,
        P.vertical (stackProfileBlend P.horizontal (reunionReflectedHorizontal P) t p.2 •
          p.1) * p.2) := by
    dsimp only [M, stackCapProfilePath]
    rw [stackProfileBlend_eq_of_eq P.vertical P.vertical t _ rfl]
  have hF (q : UnitTwoSphere) : F q =
      (reunionReflectedHorizontal P (heightCoordinates (q : E3)).2 •
        (heightCoordinates (q : E3)).1,
        P.vertical (reunionReflectedHorizontal P (heightCoordinates (q : E3)).2 •
          (heightCoordinates (q : E3)).1) * (heightCoordinates (q : E3)).2) := by
    rw [show F q = M 1 (heightCoordinates (q : E3)) from rfl, hM]
    rw [stackProfileBlend_of_one_le _ _ 1 le_rfl]
  have hb (X : E2) (_hX : ‖X‖ ≤ 1) : P.vertical X ≤ 2 * P.heightBound := by
    by_cases hfar : 1 / 2 ≤ ‖X‖
    · rw [P.vertical_far X hfar]
      linarith only [P.one_le_heightBound]
    have hx : ‖X‖ < 1 / 2 := lt_of_not_ge hfar
    have hrad : 0 ≤ 1 - ‖X‖ ^ 2 := by nlinarith [norm_nonneg X]
    let z := Real.sqrt (1 - ‖X‖ ^ 2)
    have hzsq : z ^ 2 = 1 - ‖X‖ ^ 2 := Real.sq_sqrt hrad
    have hz0 : 0 ≤ z := Real.sqrt_nonneg _
    have hzhalf : 1 / 2 ≤ z := by nlinarith [norm_nonneg X]
    let q : UnitTwoSphere := ⟨heightCoordinates.symm (X, z), by
      rw [mem_sphere_zero_iff_norm]
      have hn := heightCoordinates_symm_norm_sq (X, z)
      dsimp only [Prod.fst, Prod.snd] at hn
      nlinarith [norm_nonneg (heightCoordinates.symm (X, z))]⟩
    have hq : heightCoordinates (q : E3) = (X, z) := heightCoordinates.apply_symm_apply _
    have haz : P.horizontal z = 1 := P.horizontal_far z (by rwa [abs_of_nonneg hz0])
    have hmodel : (P.model q).2 = P.vertical X * z := by
      change (flatCapDiffeomorph _ _ _ _ _ _ (heightCoordinates (q : E3))).2 = _
      rw [hq, flatCapDiffeomorph_apply, haz, one_smul]
    have hupper : P.vertical X * z ≤ P.heightBound := by
      rw [← hmodel]
      exact (le_abs_self _).trans (P.height_bound q)
    nlinarith only [hupper, hzhalf, P.vertical_pos X]
  have hmodels (t : ℝ) (q : UnitTwoSphere) :
      ‖(M t (heightCoordinates (q : E3))).1‖ ≤ 1 ∧
      |(M t (heightCoordinates (q : E3))).2| ≤ 2 * P.heightBound := by
    have hx : ‖(M t (heightCoordinates (q : E3))).1‖ ≤ 1 :=
      stackCapProfilePath_fst_norm_le P.horizontal (reunionReflectedHorizontal P)
        P.vertical P.vertical P.horizontal_smooth hA P.vertical_smooth P.vertical_smooth
        P.horizontal_pos hApos P.vertical_pos P.vertical_pos P.horizontal_bound hAbound
        t (heightCoordinates (q : E3)) (sphere_height_coordinates_sq q).le
    have hz : |(heightCoordinates (q : E3)).2| ≤ 1 := by
      nlinarith [sphere_height_coordinates_sq q, sq_abs (heightCoordinates (q : E3)).2,
        abs_nonneg (heightCoordinates (q : E3)).2,
        sq_nonneg ‖(heightCoordinates (q : E3)).1‖]
    have hheight : (M t (heightCoordinates (q : E3))).2 =
        P.vertical (M t (heightCoordinates (q : E3))).1 * (heightCoordinates (q : E3)).2 := by
      rw [hM]
    refine ⟨hx, ?_⟩
    rw [hheight, abs_mul, abs_of_pos (P.vertical_pos _)]
    calc
      P.vertical (M t (heightCoordinates (q : E3))).1 *
          |(heightCoordinates (q : E3)).2| ≤ (2 * P.heightBound) * 1 :=
        mul_le_mul (hb _ hx) hz (abs_nonneg _) (by linarith [P.one_le_heightBound])
      _ = 2 * P.heightBound := mul_one _
  have hstationary (t : ℝ) (p : E2 × ℝ) (hp : p.2 ∉ Icc (-1 / 2 : ℝ) (-1 / 4)) :
      M t p = M 0 p := by
    rw [hM, hM, stackProfileBlend_eq_of_eq _ _ t p.2 (hAoff p.2 hp).symm,
      stackProfileBlend_eq_of_eq _ _ 0 p.2 (hAoff p.2 hp).symm]
  let flip : UnitTwoSphere → UnitTwoSphere := fun q =>
    ⟨heightCoordinates.symm ((heightCoordinates (q : E3)).1,
      -(heightCoordinates (q : E3)).2), by
      rw [mem_sphere_zero_iff_norm]
      have hn := heightCoordinates_symm_norm_sq
        ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2)
      simp only [neg_sq] at hn
      nlinarith [sphere_height_coordinates_sq q,
        norm_nonneg (heightCoordinates.symm
          ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2))]⟩
  have hflip (q : UnitTwoSphere) : heightCoordinates (flip q : E3) =
      ((heightCoordinates (q : E3)).1, -(heightCoordinates (q : E3)).2) :=
    heightCoordinates.apply_symm_apply _
  have hflipflip (q : UnitTwoSphere) : flip (flip q) = q := by
    apply Subtype.ext
    apply heightCoordinates.injective
    rw [hflip, hflip]
    simp only [neg_neg, Prod.eta]
  have hFnorth (q : UnitTwoSphere) (hq : 0 ≤ (heightCoordinates (q : E3)).2) :
      F q = P.model q := by
    rw [hF, hAnorth _ hq]
    rfl
  have hFsouth (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      F q = ((P.model (flip q)).1, -(P.model (flip q)).2) := by
    rw [hF, hAsouth _ hq]
    change (_, _) = ((flatCapDiffeomorph _ _ _ _ _ _
      (heightCoordinates (flip q : E3))).1, -(flatCapDiffeomorph _ _ _ _ _ _
        (heightCoordinates (flip q : E3))).2)
    rw [hflip, flatCapDiffeomorph_apply]
    simp only [mul_neg, neg_neg]
  have hend (q : UnitTwoSphere) : |(F q).2| ≤ P.heightBound := by
    rcases le_total 0 (heightCoordinates (q : E3)).2 with hq | hq
    · rw [hFnorth q hq]
      exact P.height_bound q
    · rw [hFsouth q hq, abs_neg]
      exact P.height_bound (flip q)
  have himage : F '' {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} =
      (fun p : E2 × ℝ => (p.1, -p.2)) ''
        (P.model '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}) := by
    ext p
    constructor
    · rintro ⟨q, hq, rfl⟩
      refine ⟨P.model (flip q), ⟨flip q, ?_, rfl⟩, (hFsouth q hq).symm⟩
      change 0 ≤ (heightCoordinates (flip q : E3)).2
      rw [hflip]
      exact neg_nonneg.mpr hq
    · rintro ⟨p, ⟨q, hq, rfl⟩, rfl⟩
      have hqs : (heightCoordinates (flip q : E3)).2 ≤ 0 := by
        rw [hflip]
        exact neg_nonpos.mpr hq
      refine ⟨flip q, hqs, ?_⟩
      rw [hFsouth (flip q) hqs, hflipflip]
  have hFc : Continuous F :=
    (stackCapProfilePath_native_contMDiff P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical P.horizontal_smooth hA P.vertical_smooth
      P.vertical_smooth).continuous.comp (continuous_const.prodMk continuous_id)
  have hzc : Continuous (fun q : UnitTwoSphere => (heightCoordinates (q : E3)).2) :=
    (heightCoordinates.continuous.comp continuous_subtype_val).snd
  have hnonpos (q : UnitTwoSphere) (hq : (heightCoordinates (q : E3)).2 ≤ 0) :
      (F q).2 ≤ 0 := by
    rw [hF]
    exact mul_nonpos_of_nonneg_of_nonpos (P.vertical_pos _).le hq
  have hlevel : {q : UnitTwoSphere | (F q).2 = 0} ⊆
      {q : UnitTwoSphere | |(heightCoordinates (q : E3)).2| < 1 / 4} := by
    intro q hq
    change (F q).2 = 0 at hq
    rw [hF] at hq
    have hz : (heightCoordinates (q : E3)).2 = 0 :=
      (mul_eq_zero.mp hq).resolve_left (P.vertical_pos _).ne'
    change |(heightCoordinates (q : E3)).2| < 1 / 4
    rw [hz]
    norm_num
  obtain ⟨δ, hδ, hδband⟩ := exists_uniform_zero_level_band
    (fun q : UnitTwoSphere => (F q).2) hFc.snd
      (isOpen_lt hzc.abs continuous_const) hlevel
  let ε := min (δ / 2) (1 / 8 : ℝ)
  have hε : 0 < ε := lt_min (by positivity) (by norm_num)
  have hεquarter : ε < 1 / 4 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith only [hδ])
  have hband (q : UnitTwoSphere) (hq : |(F q).2| ≤ ε) :
      |(heightCoordinates (q : E3)).2| < 1 / 4 := hδband q (hq.trans_lt hεδ)
  have hFmodel (q : UnitTwoSphere) : F q =
      surgeryCapModel (reunionReflectedHorizontal P) P.vertical hA P.vertical_smooth
        (fun z => (hApos z).ne') (fun X => (P.vertical_pos X).ne') q := by
    rw [hF]
    rfl
  have hcylinder (q : UnitTwoSphere) (hq : |(heightCoordinates (q : E3)).2| ≤ 1 / 4) :
      F q = ((circleDirection (heightCoordinates (q : E3)).1 : E2),
        (heightCoordinates (q : E3)).2) := by
    rw [hFmodel]
    exact surgeryCapModel_cylinder _ _ _ _ _ _ hAnear P.vertical_far q hq
  refine ⟨hb, hmodels, hstationary, hend, himage, ε, hε, hεquarter, hband, ?_⟩
  ext p
  constructor
  · rintro ⟨q, ⟨hqs, hqe⟩, rfl⟩
    have hqa : |(F q).2| ≤ ε := by rw [abs_of_nonpos (hnonpos q hqs)]; linarith only [hqe]
    have hc := hcylinder q (hband q hqa).le
    refine ⟨?_, hqe, hnonpos q hqs⟩
    change (F q).1 ∈ sphere (0 : E2) 1
    rw [hc]
    exact (circleDirection _).2
  · rcases p with ⟨θ, z⟩
    rintro ⟨hθ, hzlo, hzhi⟩
    have hθnorm : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ
    have hzabs : |z| ≤ ε := by rw [abs_of_nonpos hzhi]; linarith only [hzlo]
    have hzquarter : |z| ≤ 1 / 4 := hzabs.trans hεquarter.le
    have hrad : 0 ≤ 1 - z ^ 2 := by nlinarith [sq_abs z, abs_nonneg z]
    let X := Real.sqrt (1 - z ^ 2) • θ
    have hnorm : ‖X‖ = Real.sqrt (1 - z ^ 2) := by
      simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        hθnorm, mul_one]
    let q : UnitTwoSphere := ⟨heightCoordinates.symm (X, z), by
      rw [mem_sphere_zero_iff_norm]
      have hn := heightCoordinates_symm_norm_sq (X, z)
      dsimp only [Prod.fst, Prod.snd] at hn
      rw [hnorm] at hn
      nlinarith [Real.sq_sqrt hrad, norm_nonneg (heightCoordinates.symm (X, z))]⟩
    have hq : heightCoordinates (q : E3) = (X, z) := heightCoordinates.apply_symm_apply _
    have hFq : F q = (θ, z) := by
      rw [hFmodel]
      change flatCapDiffeomorph _ _ _ _ _ _ (heightCoordinates (q : E3)) = _
      rw [hq]
      exact flatCapDiffeomorph_cylinder _ _ _ _ _ _ hAnear P.vertical_far
        θ hθnorm z hzquarter
    refine ⟨q, ⟨?_, ?_⟩, hFq⟩
    · rw [hq]
      exact hzhi
    · change -ε ≤ (F q).2
      rw [hFq]
      exact hzlo

end PoincareConjecture.M25.Topology3D
