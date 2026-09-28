import PoincareConjecture.Proofs.M25.Topology3D.Space3.Reverse.ParentBallReferenceProfile
import PoincareConjecture.Proofs.M25.Topology3D.Space3.NorthSphereCoordinates

set_option autoImplicit false

open Set Metric
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

noncomputable def referenceCapHeight (a : ℝ) (X : E2) : ℝ :=
  ((referenceCapScale a) ^ 2 - ‖X‖ ^ 2) /
    ((referenceCapScale a) ^ 2 + ‖X‖ ^ 2)

noncomputable def referenceCapPoint (a : ℝ) (X : E2) : E3 :=
  heightCoordinates.symm
    ((2 * referenceCapScale a / ((referenceCapScale a) ^ 2 + ‖X‖ ^ 2)) • X,
      referenceCapHeight a X)

theorem referenceCapHeight_contDiff (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    ContDiff ℝ ∞ (referenceCapHeight a) := by
  apply (contDiff_const.sub (contDiff_id.norm_sq ℝ)).div
    (contDiff_const.add (contDiff_id.norm_sq ℝ))
  intro X
  exact ne_of_gt (add_pos_of_pos_of_nonneg
    (sq_pos_of_pos (referenceCapScale_pos a ha)) (sq_nonneg ‖X‖))

private theorem reference_cap_point_eq_north
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (X : E2) :
    referenceCapPoint a X = northSphereVector ((referenceCapScale a)⁻¹ • X) := by
  let c := referenceCapScale a
  have hc : 0 < c := referenceCapScale_pos a ha
  have hd : c ^ 2 + ‖X‖ ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖))
  have hn : ‖c⁻¹ • X‖ ^ 2 = ‖X‖ ^ 2 / c ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow]
    ring
  apply heightCoordinates.injective
  rw [referenceCapPoint, northSphereVector, heightCoordinates.apply_symm_apply,
    heightCoordinates.apply_symm_apply]
  change ((2 * c / (c ^ 2 + ‖X‖ ^ 2)) • X,
    (c ^ 2 - ‖X‖ ^ 2) / (c ^ 2 + ‖X‖ ^ 2)) =
      ((2 / (1 + ‖c⁻¹ • X‖ ^ 2)) • (c⁻¹ • X),
        (1 - ‖c⁻¹ • X‖ ^ 2) / (1 + ‖c⁻¹ • X‖ ^ 2))
  rw [hn, smul_smul]
  apply Prod.ext
  · congr 1
    field_simp [hc.ne', hd]
  · field_simp [hc.ne', hd]

theorem referenceCapPoint_contDiff (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    ContDiff ℝ ∞ (referenceCapPoint a) := by
  have heq : referenceCapPoint a =
      fun X => northSphereVector ((referenceCapScale a)⁻¹ • X) :=
    funext (reference_cap_point_eq_north a ha)
  rw [heq]
  have hscale : ContDiff ℝ ∞ (fun X : E2 => (referenceCapScale a)⁻¹ • X) :=
    contDiff_const_smul _
  exact northSphereVector_contDiff.comp hscale

theorem referenceCapPoint_mem_sphere
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (X : E2) :
    referenceCapPoint a X ∈ sphere (0 : E3) 1 := by
  rw [mem_sphere_zero_iff_norm, reference_cap_point_eq_north a ha]
  exact northSphereVector_norm _

theorem referenceCapPoint_cap_iff
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (X : E2) :
    a ≤ (heightCoordinates (referenceCapPoint a X)).2 ↔ ‖X‖ ≤ 1 := by
  let c := referenceCapScale a
  have hc : 0 < c := referenceCapScale_pos a ha
  have hscale : c ^ 2 * (1 - a) = 1 + a := referenceCapScale_sq a ha
  have hnum : 0 < 1 + a := by linarith only [ha.1]
  have hd : 0 < c ^ 2 + ‖X‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖)
  have heq : c ^ 2 - ‖X‖ ^ 2 - a * (c ^ 2 + ‖X‖ ^ 2) =
      (1 + a) * (1 - ‖X‖ ^ 2) := by nlinarith only [hscale]
  rw [referenceCapPoint, heightCoordinates.apply_symm_apply]
  change a ≤ (c ^ 2 - ‖X‖ ^ 2) / (c ^ 2 + ‖X‖ ^ 2) ↔ ‖X‖ ≤ 1
  rw [le_div_iff₀ hd, ← sub_nonneg, heq,
    mul_nonneg_iff_of_pos_left hnum, sub_nonneg]
  simpa only [one_pow] using (sq_le_sq₀ (norm_nonneg X) zero_le_one)

theorem referenceCapPoint_rim_iff
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) (X : E2) :
    (heightCoordinates (referenceCapPoint a X)).2 = a ↔ ‖X‖ = 1 := by
  let c := referenceCapScale a
  have hc : 0 < c := referenceCapScale_pos a ha
  have hscale : c ^ 2 * (1 - a) = 1 + a := referenceCapScale_sq a ha
  have hnum : 0 < 1 + a := by linarith only [ha.1]
  have hd : c ^ 2 + ‖X‖ ^ 2 ≠ 0 :=
    ne_of_gt (add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖))
  rw [referenceCapPoint, heightCoordinates.apply_symm_apply]
  change (c ^ 2 - ‖X‖ ^ 2) / (c ^ 2 + ‖X‖ ^ 2) = a ↔ ‖X‖ = 1
  rw [div_eq_iff hd]
  constructor
  · intro h
    have hprod : (1 + a) * (1 - ‖X‖ ^ 2) = 0 := by nlinarith only [hscale, h]
    have hsq : 1 - ‖X‖ ^ 2 = 0 := (mul_eq_zero.mp hprod).resolve_left hnum.ne'
    nlinarith only [hsq, norm_nonneg X]
  · intro h
    rw [h, one_pow]
    nlinarith only [hscale]

theorem referenceCapPoint_image_closedBall
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1) :
    referenceCapPoint a '' closedBall (0 : E2) 1 =
      {y : E3 | ‖y‖ = 1 ∧ a ≤ (heightCoordinates y).2} := by
  ext y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact ⟨mem_sphere_zero_iff_norm.mp (referenceCapPoint_mem_sphere a ha X),
      (referenceCapPoint_cap_iff a ha X).mpr (mem_closedBall_zero_iff.mp hX)⟩
  · rintro ⟨hynorm, hycap⟩
    let q : UnitTwoSphere := ⟨y, mem_sphere_zero_iff_norm.mpr hynorm⟩
    have hq : q ∈ northSphereDomain := by
      change -1 < (heightCoordinates y).2
      linarith only [ha.1, hycap]
    let c := referenceCapScale a
    have hc : 0 < c := referenceCapScale_pos a ha
    let X := c • northSphereCoordinate q
    have hXeq : referenceCapPoint a X = y := by
      rw [reference_cap_point_eq_north a ha]
      have hcancel : (referenceCapScale a)⁻¹ • X = northSphereCoordinate q := by
        change c⁻¹ • (c • northSphereCoordinate q) = northSphereCoordinate q
        rw [smul_smul, inv_mul_cancel₀ hc.ne', one_smul]
      rw [hcancel]
      exact congrArg Subtype.val (northSpherePoint_coordinate hq)
    refine ⟨X, mem_closedBall_zero_iff.mpr ?_, hXeq⟩
    apply (referenceCapPoint_cap_iff a ha X).mp
    rwa [hXeq]

noncomputable def referenceFlatteningDiffeomorph
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z) :
    Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ) (E2 × ℝ) (E2 × ℝ) ∞ := by
  let H := ((ContinuousLinearEquiv.prodComm ℝ E2 ℝ).toDiffeomorph.trans
    (fiberScalingDiffeomorph α hα (fun z => (hpos z).ne'))).trans
      (ContinuousLinearEquiv.prodComm ℝ ℝ E2).toDiffeomorph
  let V : Diffeomorph 𝓘(ℝ, E2 × ℝ) 𝓘(ℝ, E2 × ℝ)
      (E2 × ℝ) (E2 × ℝ) ∞ := {
    toEquiv := {
      toFun := fun p => (p.1, p.2 - referenceCapHeight a p.1)
      invFun := fun p => (p.1, p.2 + referenceCapHeight a p.1)
      left_inv := fun p => Prod.ext rfl (sub_add_cancel p.2 _)
      right_inv := fun p => Prod.ext rfl (add_sub_cancel_right p.2 _) }
    contMDiff_toFun := (contDiff_fst.prodMk
      (contDiff_snd.sub ((referenceCapHeight_contDiff a ha).comp contDiff_fst))).contMDiff
    contMDiff_invFun := (contDiff_fst.prodMk
      (contDiff_snd.add ((referenceCapHeight_contDiff a ha).comp contDiff_fst))).contMDiff }
  exact H.trans V

@[simp] theorem referenceFlatteningDiffeomorph_apply
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z) (p : E2 × ℝ) :
    referenceFlatteningDiffeomorph a ha α hα hpos p =
      (α p.2 • p.1, p.2 - referenceCapHeight a (α p.2 • p.1)) := rfl

@[simp] theorem referenceFlatteningDiffeomorph_symm_apply
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z) (p : E2 × ℝ) :
    (referenceFlatteningDiffeomorph a ha α hα hpos).symm p =
      ((α (p.2 + referenceCapHeight a p.1))⁻¹ • p.1,
        p.2 + referenceCapHeight a p.1) := rfl

private theorem reference_model_comparison
    (c k r z : ℝ) (hc : 0 < c) (hk : 0 < k) (_hr : 0 ≤ r)
    (hzlo : -1 < z) (hzhi : z ≤ 1)
    (hkbound : k ≤ c / (1 + z)) (hball : r ^ 2 + z ^ 2 ≤ 1) :
    (k * r) ^ 2 * (1 + z) ≤ c ^ 2 * (1 - z) ∧
      (r ^ 2 + z ^ 2 < 1 → (k * r) ^ 2 * (1 + z) < c ^ 2 * (1 - z)) := by
  have hu : 0 < 1 + z := by linarith only [hzlo]
  have hv : 0 ≤ 1 - z := sub_nonneg.mpr hzhi
  have hku : k * (1 + z) ≤ c := (le_div_iff₀ hu).mp hkbound
  have hsq : k ^ 2 * (1 + z) ^ 2 ≤ c ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (mul_nonneg hk.le hu.le) hc.le).mpr hku
  have hweight : 0 < k ^ 2 * (1 + z) := mul_pos (sq_pos_of_pos hk) hu
  have hsecond := mul_le_mul_of_nonneg_right hsq hv
  have hrbound : r ^ 2 ≤ (1 + z) * (1 - z) := by nlinarith only [hball]
  constructor
  · have hfirst := mul_le_mul_of_nonneg_left hrbound hweight.le
    nlinarith only [hfirst, hsecond]
  · intro hstrict
    have hrstrict : r ^ 2 < (1 + z) * (1 - z) := by nlinarith only [hstrict]
    have hfirst := mul_lt_mul_of_pos_left hrstrict hweight
    nlinarith only [hfirst, hsecond]

theorem referenceFlattening_snd_mem_Icc
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (hcompare : ∀ z, -1 < z → z ≤ 1 → α z ≤ referenceCapScale a / (1 + z))
    (p : E2 × ℝ) (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 ≤ 1) :
    (referenceFlatteningDiffeomorph a ha α hα hpos p).2 ∈ Icc (-2 : ℝ) 0 := by
  let c := referenceCapScale a
  let X := α p.2 • p.1
  have hc : 0 < c := referenceCapScale_pos a ha
  have hd : 0 < c ^ 2 + ‖X‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖)
  have hheight : referenceCapHeight a X ≤ 1 := by
    apply (div_le_one hd).mpr
    linarith only [sq_nonneg ‖X‖]
  have hzlo : -1 ≤ p.2 := by nlinarith only [hp, sq_nonneg ‖p.1‖]
  have hzhi : p.2 ≤ 1 := by nlinarith only [hp, sq_nonneg ‖p.1‖]
  rw [referenceFlatteningDiffeomorph_apply]
  change -2 ≤ p.2 - referenceCapHeight a X ∧ p.2 - referenceCapHeight a X ≤ 0
  refine ⟨by linarith only [hheight, hzlo], ?_⟩
  by_cases hz : -1 < p.2
  · have hcomp := (reference_model_comparison c (α p.2) ‖p.1‖ p.2 hc
      (hpos p.2) (norm_nonneg p.1) hz hzhi (hcompare p.2 hz hzhi) hp).1
    have hnorm : ‖X‖ = α p.2 * ‖p.1‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos p.2)]
    have hle : p.2 ≤ referenceCapHeight a X := by
      apply (le_div_iff₀ hd).mpr
      rw [hnorm]
      nlinarith only [hcomp]
    exact sub_nonpos.mpr hle
  · have hzneg : p.2 = -1 := le_antisymm (le_of_not_gt hz) hzlo
    have hxnorm : ‖p.1‖ = 0 := by
      rw [hzneg] at hp
      nlinarith only [hp, norm_nonneg p.1]
    have hx : p.1 = 0 := norm_eq_zero.mp hxnorm
    have hXzero : X = 0 := by simp only [X, hx, smul_zero]
    have hhzero : referenceCapHeight a (0 : E2) = 1 := by
      simp only [referenceCapHeight, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
        sub_zero, add_zero]
      exact div_self (pow_ne_zero 2 hc.ne')
    rw [hXzero, hhzero, hzneg]
    norm_num

theorem referenceFlattening_snd_neg
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (hcompare : ∀ z, -1 < z → z ≤ 1 → α z ≤ referenceCapScale a / (1 + z))
    (p : E2 × ℝ) (hp : ‖p.1‖ ^ 2 + p.2 ^ 2 < 1) :
    (referenceFlatteningDiffeomorph a ha α hα hpos p).2 < 0 := by
  let c := referenceCapScale a
  let X := α p.2 • p.1
  have hc : 0 < c := referenceCapScale_pos a ha
  have hd : 0 < c ^ 2 + ‖X‖ ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖)
  have hzlo : -1 < p.2 := by nlinarith only [hp, sq_nonneg ‖p.1‖]
  have hzhi : p.2 ≤ 1 := by nlinarith only [hp, sq_nonneg ‖p.1‖]
  have hcomp := (reference_model_comparison c (α p.2) ‖p.1‖ p.2 hc
    (hpos p.2) (norm_nonneg p.1) hzlo hzhi (hcompare p.2 hzlo hzhi) hp.le).2 hp
  have hnorm : ‖X‖ = α p.2 * ‖p.1‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos p.2)]
  have hlt : p.2 < referenceCapHeight a X := by
    apply (lt_div_iff₀ hd).mpr
    rw [hnorm]
    nlinarith only [hcomp]
  rw [referenceFlatteningDiffeomorph_apply]
  exact sub_neg.mpr hlt

theorem referenceFlattening_capPoint
    (a : ℝ) (ha : a ∈ Ioo (1 / 2 : ℝ) 1)
    (α : ℝ → ℝ) (hα : ContDiff ℝ ∞ α) (hpos : ∀ z, 0 < α z)
    (c₂ : ℝ) (heq : ∀ z, c₂ ≤ z → α z = referenceCapScale a / (1 + z))
    (X : E2) (hX : c₂ ≤ referenceCapHeight a X) :
    referenceFlatteningDiffeomorph a ha α hα hpos
      (heightCoordinates (referenceCapPoint a X)) = (X, 0) := by
  let c := referenceCapScale a
  let d := c ^ 2 + ‖X‖ ^ 2
  have hc : 0 < c := referenceCapScale_pos a ha
  have hd : 0 < d := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg ‖X‖)
  have hh : 1 + referenceCapHeight a X = 2 * c ^ 2 / d := by
    change 1 + (c ^ 2 - ‖X‖ ^ 2) / d = 2 * c ^ 2 / d
    field_simp [hd.ne']
    dsimp only [d]
    ring
  have hfactor : α (referenceCapHeight a X) * (2 * c / d) = 1 := by
    rw [heq _ hX, hh]
    change c / (2 * c ^ 2 / d) * (2 * c / d) = 1
    field_simp [hc.ne', hd.ne']
  have hhorizontal : α (referenceCapHeight a X) • ((2 * c / d) • X) = X := by
    rw [smul_smul, hfactor, one_smul]
  rw [referenceFlatteningDiffeomorph_apply, referenceCapPoint,
    heightCoordinates.apply_symm_apply]
  change (α (referenceCapHeight a X) • ((2 * c / d) • X),
    referenceCapHeight a X - referenceCapHeight a
      (α (referenceCapHeight a X) • ((2 * c / d) • X))) = (X, 0)
  rw [hhorizontal, sub_self]

end PoincareConjecture.M25.Topology3D
