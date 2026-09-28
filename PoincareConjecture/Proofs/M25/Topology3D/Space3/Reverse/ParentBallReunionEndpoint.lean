import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionAxial
import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReunionProfile

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold Topology InnerProductSpace

namespace PoincareConjecture.M25.Topology3D

theorem reunion_axial_endpoint_image (P : SurgeryCapProfile)
    (a lambda ε : ℝ) (ha : 0 < a) (hlambda : 0 < lambda)
    (hε : 0 < ε) (hεquarter : ε < 1 / 4)
    (hband : ∀ q : UnitTwoSphere,
      |(stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
        P.vertical P.vertical 1 (heightCoordinates (q : E3))).2| ≤ ε →
      |(heightCoordinates (q : E3)).2| < 1 / 4) :
    let F := fun q : UnitTwoSphere =>
      stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
        P.vertical P.vertical 1 (heightCoordinates (q : E3))
    (fun q : UnitTwoSphere =>
      ((F q).1, a + reunionAxialHeight a lambda ε 1 (F q).2)) ''
        {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0} =
      (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ)) ∪
      (sphere (0 : E2) 1 ×ˢ Ioo (-a) a) ∪
      ((fun p : E2 × ℝ => (p.1, -a - lambda * p.2)) ''
        (P.model '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2})) := by
  obtain ⟨hA, hApos, hAnear, _hAfar, _hAbound, _hAnorth, _hAsouth, _hAoff⟩ :=
    reunionReflectedHorizontal_spec P
  let F := fun q : UnitTwoSphere =>
    stackCapProfilePath P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical 1 (heightCoordinates (q : E3))
  let Qminus := {q : UnitTwoSphere | (heightCoordinates (q : E3)).2 ≤ 0}
  let S := F '' Qminus
  let N := P.model '' {q : UnitTwoSphere | 0 ≤ (heightCoordinates (q : E3)).2}
  let H := fun Z : ℝ => a + reunionAxialHeight a lambda ε 1 Z
  let f := fun p : E2 × ℝ => (p.1, H p.2)
  let opposite := fun p : E2 × ℝ => (p.1, -a + lambda * p.2)
  have hSneg (p : E2 × ℝ) (hp : p ∈ S) : p.2 ≤ 0 := by
    rcases hp with ⟨q, hq, rfl⟩
    exact stackCapProfilePath_snd_nonpos P.horizontal (reunionReflectedHorizontal P)
      P.vertical P.vertical P.vertical_pos P.vertical_pos 1
      (heightCoordinates (q : E3)) hq
  have hFmodel (q : UnitTwoSphere) : F q =
      surgeryCapModel (reunionReflectedHorizontal P) P.vertical hA P.vertical_smooth
        (fun z => (hApos z).ne') (fun X => (P.vertical_pos X).ne') q := by
    simp only [F, stackCapProfilePath, stackProfileBlend_of_one_le _ _ 1 le_rfl,
      surgeryCapModel, flatCapDiffeomorph_apply]
  have hScircle (p : E2 × ℝ) (hp : p ∈ S) (hz : -ε ≤ p.2) : p.1 ∈ sphere (0 : E2) 1 := by
    have hpneg := hSneg p hp
    rcases hp with ⟨q, hq, rfl⟩
    have hqa : |(F q).2| ≤ ε := by rw [abs_of_nonpos hpneg]; linarith only [hz]
    have hc : F q = ((circleDirection (heightCoordinates (q : E3)).1 : E2),
        (heightCoordinates (q : E3)).2) := by
      rw [hFmodel]
      exact surgeryCapModel_cylinder _ _ _ _ _ _ hAnear P.vertical_far q (hband q hqa).le
    rw [hc]
    exact (circleDirection _).2
  have hCylinder : sphere (0 : E2) 1 ×ˢ Icc (-ε) 0 ⊆ S := by
    rintro ⟨θ, Z⟩ ⟨hθ, hZlo, hZhi⟩
    have hθnorm : ‖θ‖ = 1 := mem_sphere_zero_iff_norm.mp hθ
    have hZabs : |Z| ≤ ε := by rw [abs_of_nonpos hZhi]; linarith only [hZlo]
    have hZquarter : |Z| ≤ 1 / 4 := hZabs.trans hεquarter.le
    have hrad : 0 ≤ 1 - Z ^ 2 := by nlinarith [sq_abs Z, abs_nonneg Z]
    let X := Real.sqrt (1 - Z ^ 2) • θ
    have hnorm : ‖X‖ = Real.sqrt (1 - Z ^ 2) := by
      simp only [X, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
        hθnorm, mul_one]
    let q : UnitTwoSphere := ⟨heightCoordinates.symm (X, Z), by
      rw [mem_sphere_zero_iff_norm]
      have hn := heightCoordinates_symm_norm_sq (X, Z)
      dsimp only [Prod.fst, Prod.snd] at hn
      rw [hnorm] at hn
      nlinarith [Real.sq_sqrt hrad, norm_nonneg (heightCoordinates.symm (X, Z))]⟩
    have hq : heightCoordinates (q : E3) = (X, Z) := heightCoordinates.apply_symm_apply _
    refine ⟨q, ?_, ?_⟩
    · change (heightCoordinates (q : E3)).2 ≤ 0
      rw [hq]
      exact hZhi
    · rw [hFmodel]
      change flatCapDiffeomorph _ _ _ _ _ _ (heightCoordinates (q : E3)) = _
      rw [hq]
      exact flatCapDiffeomorph_cylinder _ _ _ _ _ _ hAnear P.vertical_far
        θ hθnorm Z hZquarter
  have hSN : S = (fun p : E2 × ℝ => (p.1, -p.2)) '' N :=
    (reunion_reflected_model_spec P).2.2.2.2.1
  have hOpposite : (fun p : E2 × ℝ => (p.1, -a - lambda * p.2)) '' N =
      opposite '' S := by
    rw [hSN, image_image opposite (fun p : E2 × ℝ => (p.1, -p.2)) N]
    apply image_congr
    intro p _hp
    change (p.1, -a - lambda * p.2) = (p.1, -a + lambda * -p.2)
    congr 1
    ring
  obtain ⟨hg, _hderiv, hbij, _hbounds, htail, hfixed, _hzero, _hone⟩ :=
    reunionAxialHeight_spec a lambda ε ha hlambda hε
  have hHc : Continuous H := continuous_const.add
    ((hg.comp (contDiff_const.prodMk contDiff_id)).continuous)
  have hHm : StrictMono H := by
    intro x y hxy
    dsimp only [H]
    linarith only [(hbij 1).1 hxy]
  have hHdeep (Z : ℝ) (hZ : Z ≤ -ε) : H Z = -a + lambda * Z := by
    dsimp only [H]
    rw [htail 1 Z hZ, Real.smoothTransition.one]
    ring
  have hHlo : H (-ε) = -a - lambda * ε := by rw [hHdeep _ le_rfl]; ring
  have hHhi : H 0 = a := by
    dsimp only [H]
    rw [hfixed 1 0 (by linarith only [hε]), mul_zero, add_zero]
  have hHpre (w : ℝ) (hw : w ∈ Icc (-a - lambda * ε) a) :
      ∃ Z ∈ Icc (-ε) 0, H Z = w := by
    apply intermediate_value_Icc (by linarith only [hε]) hHc.continuousOn
    simpa only [hHlo, hHhi] using hw
  change (f ∘ F) '' Qminus = _
  rw [image_comp]
  change f '' S = (sphere (0 : E2) 1 ×ˢ ({a} : Set ℝ)) ∪
    (sphere (0 : E2) 1 ×ˢ Ioo (-a) a) ∪
    ((fun p : E2 × ℝ => (p.1, -a - lambda * p.2)) '' N)
  rw [hOpposite]
  ext y
  constructor
  · rintro ⟨p, hp, rfl⟩
    by_cases hdeep : p.2 ≤ -ε
    · right
      exact ⟨p, hp, Prod.ext rfl (hHdeep p.2 hdeep).symm⟩
    have hpZ : p.2 ∈ Icc (-ε) 0 := ⟨(lt_of_not_ge hdeep).le, hSneg p hp⟩
    have hθ := hScircle p hp hpZ.1
    have hlow : -a - lambda * ε ≤ H p.2 := by rw [← hHlo]; exact hHm.monotone hpZ.1
    have hhigh : H p.2 ≤ a := by rw [← hHhi]; exact hHm.monotone hpZ.2
    by_cases htop : H p.2 = a
    · left
      left
      exact ⟨hθ, mem_singleton_iff.mpr htop⟩
    by_cases hmid : -a < H p.2
    · left
      right
      exact ⟨hθ, hmid, lt_of_le_of_ne hhigh htop⟩
    right
    let Z := (H p.2 + a) / lambda
    have hZlo : -ε ≤ Z := (le_div_iff₀ hlambda).mpr (by nlinarith only [hlow])
    have hZhi : Z ≤ 0 := div_nonpos_of_nonpos_of_nonneg
      (by linarith only [le_of_not_gt hmid]) hlambda.le
    refine ⟨(p.1, Z), hCylinder ⟨hθ, hZlo, hZhi⟩, ?_⟩
    apply Prod.ext
    · rfl
    · change -a + lambda * ((H p.2 + a) / lambda) = H p.2
      rw [mul_div_cancel₀ _ hlambda.ne']
      ring
  · intro hy
    rcases hy with (hyGamma | hyAnnulus) | hyOpposite
    · refine ⟨(y.1, 0), hCylinder ⟨hyGamma.1, by linarith only [hε], le_rfl⟩, ?_⟩
      apply Prod.ext
      · rfl
      · change H 0 = y.2
        rw [hHhi, mem_singleton_iff.mp hyGamma.2]
    · have hlow : -a - lambda * ε ≤ y.2 := by
        nlinarith only [hyAnnulus.2.1, mul_pos hlambda hε]
      obtain ⟨Z, hZ, hZw⟩ := hHpre y.2 ⟨hlow, hyAnnulus.2.2.le⟩
      exact ⟨(y.1, Z), hCylinder ⟨hyAnnulus.1, hZ⟩, Prod.ext rfl hZw⟩
    · rcases hyOpposite with ⟨p, hp, rfl⟩
      by_cases hdeep : p.2 ≤ -ε
      · exact ⟨p, hp, Prod.ext rfl (hHdeep p.2 hdeep)⟩
      have hplo : -ε ≤ p.2 := (lt_of_not_ge hdeep).le
      have hphi := hSneg p hp
      have hθ := hScircle p hp hplo
      have hlo : -a - lambda * ε ≤ -a + lambda * p.2 := by
        have h := mul_le_mul_of_nonneg_left hplo hlambda.le
        linarith only [h]
      have hhi : -a + lambda * p.2 ≤ a := by
        have h := mul_nonpos_of_nonneg_of_nonpos hlambda.le hphi
        linarith only [h, ha]
      obtain ⟨Z, hZ, hZw⟩ := hHpre (-a + lambda * p.2) ⟨hlo, hhi⟩
      exact ⟨(p.1, Z), hCylinder ⟨hθ, hZ⟩, Prod.ext rfl hZw⟩

end PoincareConjecture.M25.Topology3D
