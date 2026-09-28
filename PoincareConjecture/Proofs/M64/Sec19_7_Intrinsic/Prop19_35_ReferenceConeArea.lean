import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_PolarSectorArea

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped ENNReal Topology

namespace PoincareConjecture

theorem m64Intrinsic_reference_polar_sector_eq
    {R a : ℝ} (hR : 0 < R) (ha : a ∈ Ioo (0 : ℝ) Real.pi) :
    polarCoord.symm '' (Ioo (0 : ℝ) R ×ˢ Ioo 0 a) =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧ 0 < p.2 ∧
        0 < Real.sin a * p.1 - Real.cos a * p.2} := by
  ext p
  constructor
  · rintro ⟨⟨r, t⟩, ⟨hr, ht⟩, rfl⟩
    change (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 < R ^ 2 ∧
      0 < r * Real.sin t ∧
      0 < Real.sin a * (r * Real.cos t) - Real.cos a * (r * Real.sin t)
    have hnorm : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by
      calc
        _ = r ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
        _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    refine ⟨by rw [hnorm]; nlinarith [hr.1, hr.2],
      mul_pos hr.1 (Real.sin_pos_of_pos_of_lt_pi ht.1 (ht.2.trans ha.2)), ?_⟩
    have hdet : Real.sin a * (r * Real.cos t) - Real.cos a * (r * Real.sin t) =
        r * Real.sin (a - t) := by rw [Real.sin_sub]; ring
    rw [hdet]
    exact mul_pos hr.1 (Real.sin_pos_of_pos_of_lt_pi (sub_pos.mpr ht.2)
      (by linarith [ht.1, ha.2]))
  · rcases p with ⟨x, y⟩
    rintro ⟨hnorm, hy, hdet⟩
    have hsource : (x, y) ∈ polarCoord.source := Or.inr hy.ne'
    let P := polarCoord (x, y)
    have hP : 0 < P.1 ∧ -Real.pi < P.2 ∧ P.2 < Real.pi := polarCoord.map_source hsource
    have hxy : (P.1 * Real.cos P.2, P.1 * Real.sin P.2) = (x, y) :=
      polarCoord.left_inv hsource
    have hx : x = P.1 * Real.cos P.2 := (congrArg Prod.fst hxy).symm
    have hy' : y = P.1 * Real.sin P.2 := (congrArg Prod.snd hxy).symm
    have hsin : 0 < Real.sin P.2 := (mul_pos_iff_of_pos_left hP.1).mp (hy' ▸ hy)
    have ht : 0 < P.2 := by
      by_contra h
      have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le (le_of_not_gt h) hP.2.1.le
      linarith
    have hdet' : Real.sin a * x - Real.cos a * y = P.1 * Real.sin (a - P.2) := by
      rw [hx, hy', Real.sin_sub]
      ring
    have hsin' : 0 < Real.sin (a - P.2) :=
      (mul_pos_iff_of_pos_left hP.1).mp (hdet' ▸ hdet)
    have hta : P.2 < a := by
      by_contra h
      have hnonpos := Real.sin_nonpos_of_nonpos_of_neg_pi_le
        (sub_nonpos.mpr (le_of_not_gt h)) (by linarith [ha.1, hP.2.2])
      linarith
    have hnorm' : x ^ 2 + y ^ 2 = P.1 ^ 2 := by
      rw [hx, hy']
      calc
        _ = P.1 ^ 2 * (Real.cos P.2 ^ 2 + Real.sin P.2 ^ 2) := by ring
        _ = P.1 ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
    refine ⟨P, ⟨⟨hP.1, ?_⟩, ht, hta⟩, hxy⟩
    rw [hnorm'] at hnorm
    nlinarith

theorem m64Intrinsic_reference_halfplane_sector_volume
    {R a : ℝ} (hR : 0 < R) (ha : a ∈ Ioo (0 : ℝ) Real.pi) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧ 0 < p.2 ∧
      0 < Real.sin a * p.1 - Real.cos a * p.2} =
        ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal a := by
  rw [← m64Intrinsic_reference_polar_sector_eq hR ha]
  simpa only [sub_zero] using
    m64Intrinsic_polar_sector_volume hR (neg_nonpos.mpr Real.pi_pos.le) ha.2.le

theorem m64Intrinsic_reference_positive_cone_iff
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) Real.pi) (p : ℝ × ℝ) :
    (0 < p.2 ∧ 0 < Real.sin a * p.1 - Real.cos a * p.2) ↔
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ p = (s + t * Real.cos a, t * Real.sin a) := by
  have hsin := Real.sin_pos_of_pos_of_lt_pi ha.1 ha.2
  constructor
  · rintro ⟨hp, hdet⟩
    refine ⟨(Real.sin a * p.1 - Real.cos a * p.2) / Real.sin a,
      p.2 / Real.sin a, div_pos hdet hsin, div_pos hp hsin, ?_⟩
    apply Prod.ext
    · dsimp
      field_simp
      ring
    · dsimp
      exact (div_mul_cancel₀ p.2 hsin.ne').symm
  · rintro ⟨s, t, hs, ht, rfl⟩
    change 0 < t * Real.sin a ∧
      0 < Real.sin a * (s + t * Real.cos a) - Real.cos a * (t * Real.sin a)
    refine ⟨mul_pos ht hsin, ?_⟩
    have heq : Real.sin a * (s + t * Real.cos a) - Real.cos a * (t * Real.sin a) =
        Real.sin a * s := by ring
    rw [heq]
    exact mul_pos hsin hs

theorem m64Intrinsic_reference_positive_cone_volume
    {R a : ℝ} (hR : 0 < R) (ha : a ∈ Ioo (0 : ℝ) Real.pi) :
    volume {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ p = (s + t * Real.cos a, t * Real.sin a)} =
        ENNReal.ofReal (R ^ 2 / 2) * ENNReal.ofReal a := by
  have heq : {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧
      ∃ s t : ℝ, 0 < s ∧ 0 < t ∧ p = (s + t * Real.cos a, t * Real.sin a)} =
      {p : ℝ × ℝ | p.1 ^ 2 + p.2 ^ 2 < R ^ 2 ∧ 0 < p.2 ∧
        0 < Real.sin a * p.1 - Real.cos a * p.2} := by
    ext p
    exact and_congr_right (fun _ => (m64Intrinsic_reference_positive_cone_iff ha p).symm)
  rw [heq]
  exact m64Intrinsic_reference_halfplane_sector_volume hR ha

end PoincareConjecture
