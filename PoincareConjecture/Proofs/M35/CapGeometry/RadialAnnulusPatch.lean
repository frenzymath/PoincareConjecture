import PoincareConjecture.Proofs.M35.Thm12_28.PolarCoordinates











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M35

private theorem polar_positive_smul (q₀ q : UnitTwoSphere) {r : ℝ} (hr : 0 < r) :
    spherePolarMap q₀ (r • q.val) = (q, r - 1) := by
  have hnorm : ‖r • q.val‖ = r := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, norm_eq_of_mem_sphere, mul_one]
  have hne : r • q.val ≠ 0 := norm_ne_zero_iff.mp (hnorm.trans_ne hr.ne')
  apply Prod.ext
  · apply Subtype.ext
    simp only [spherePolarMap, dif_neg hne, hnorm, smul_smul,
      inv_mul_cancel₀ hr.ne', one_smul]
  · simp only [spherePolarMap, dif_neg hne, hnorm]



noncomputable def radialAnnulusPatch (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length) :
    StandardCylinderPatch length (a • q₀.val) := by
  let : Fact (Module.finrank ℝ StandardCapSpace = 2 + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  let f : StandardCylinderSpace → StandardCapSpace := fun z => (a + b * z.2) • z.1.val
  let inv : StandardCapSpace → StandardCylinderSpace := fun x =>
    ((spherePolarMap q₀ x).1, (‖x‖ - a) / b)
  let U : Set StandardCapSpace := {x | a - b * length < ‖x‖ ∧ ‖x‖ < a + b * length}
  have hpos (z : StandardCylinderSpace) (hz : z.2 ∈ Ioo (-length) length) :
      0 < a + b * z.2 := by
    have h := mul_lt_mul_of_pos_left hz.1 hb
    linarith
  have hnorm (z : StandardCylinderSpace) (hz : z.2 ∈ Ioo (-length) length) :
      ‖f z‖ = a + b * z.2 := by
    change ‖(a + b * z.2) • z.1.val‖ = a + b * z.2
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (hpos z hz),
      norm_eq_of_mem_sphere, mul_one]
  have hinv (x : StandardCapSpace) (hx : x ∈ U) :
      (inv x).2 ∈ Ioo (-length) length := by
    change -length < (‖x‖ - a) / b ∧ (‖x‖ - a) / b < length
    exact ⟨(lt_div_iff₀ hb).mpr (by linarith [hx.1]),
      (div_lt_iff₀ hb).mpr (by linarith [hx.2])⟩
  have hright (x : StandardCapSpace) (hx : x ∈ U) : f (inv x) = x := by
    have hn : 0 < ‖x‖ := hinner.trans hx.1
    have hne : x ≠ 0 := norm_pos_iff.mp hn
    have hc : a + b * ((‖x‖ - a) / b) = ‖x‖ := by field_simp [hb.ne']; ring
    simp only [f, inv, spherePolarMap, dif_neg hne, hc, smul_smul,
      mul_inv_cancel₀ hn.ne', one_smul]
  refine {
    length_pos := hl
    carrier := U
    carrier_open := (isOpen_Ioo.preimage continuous_norm)
    coordinate := f
    inverse := inv
    coordinate_image := ?_
    coordinate_left_inverse := ?_
    coordinate_right_inverse := hright
    inverse_domain := hinv
    coordinate_smooth := ?_
    inverse_smooth := ?_
    center_sphere := ⟨q₀, by simp [f]⟩
  }
  · apply Subset.antisymm
    · rintro x ⟨z, hz, rfl⟩
      change a - b * length < ‖f z‖ ∧ ‖f z‖ < a + b * length
      rw [hnorm z hz.2]
      constructor
      · have h := mul_lt_mul_of_pos_left hz.2.1 hb
        linarith
      · have h := mul_lt_mul_of_pos_left hz.2.2 hb
        linarith
    · intro x hx
      exact ⟨inv x, ⟨mem_univ _, hinv x hx⟩, hright x hx⟩
  · intro z hz
    apply Prod.ext
    · change (spherePolarMap q₀ ((a + b * z.2) • z.1.val)).1 = z.1
      rw [polar_positive_smul q₀ z.1 (hpos z hz.2)]
    · change (‖f z‖ - a) / b = z.2
      rw [hnorm z hz.2]
      field_simp [hb.ne']
      ring
  · have hs : ContMDiff ((𝓡 2).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞
        (fun z : StandardCylinderSpace => a + b * z.2) :=
      ((contDiff_const.add (contDiff_const.mul contDiff_id)).contMDiff).comp contMDiff_snd
    exact (hs.smul ((contMDiff_coe_sphere (n := 2) (E := StandardCapSpace)).comp
      contMDiff_fst)).contMDiffOn
  · intro x hx
    have hn : 0 < ‖x‖ := hinner.trans hx.1
    have hne : x ≠ 0 := norm_pos_iff.mp hn
    have hdir := (spherePolarMap_contMDiffAt q₀ hne).fst
    have haxis : ContMDiffAt (𝓡 3) 𝓘(ℝ, ℝ) ∞
        (fun y : StandardCapSpace => (‖y‖ - a) / b) x :=
      (((contDiffAt_norm ℝ hne).sub contDiffAt_const).div_const b).contMDiffAt
    exact (hdir.prodMk haxis).contMDiffWithinAt


theorem radialAnnulusPatch_centralSphere (q₀ : UnitTwoSphere) (a b length : ℝ)
    (hb : 0 < b) (hl : 0 < length) (hinner : 0 < a - b * length) :
    (radialAnnulusPatch q₀ a b length hb hl hinner).centralSphere = Metric.sphere 0 a := by
  have ha : 0 < a := by nlinarith [mul_pos hb hl]
  ext x
  change (∃ z : StandardCylinderSpace, z ∈ univ ×ˢ ({0} : Set ℝ) ∧
      (a + b * z.2) • z.1.val = x) ↔ x ∈ Metric.sphere 0 a
  simp only [Prod.exists, mem_prod, mem_univ, mem_singleton_iff, true_and,
    exists_eq_left, mul_zero, add_zero, Metric.mem_sphere, dist_zero_right]
  constructor
  · rintro ⟨q, rfl⟩
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos ha, norm_eq_of_mem_sphere, mul_one]
  · intro hx
    let q : UnitTwoSphere := ⟨a⁻¹ • x, by
      simp only [Metric.mem_sphere, dist_zero_right, norm_smul, Real.norm_eq_abs,
        abs_inv, abs_of_pos ha, hx, inv_mul_cancel₀ ha.ne']⟩
    exact ⟨q, by simp only [q, smul_smul, mul_inv_cancel₀ ha.ne', one_smul]⟩

end PoincareConjecture.M35
