import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Split.Marked.ShearPair



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split

private abbrev E2 := EuclideanSpace Real (Fin 2)
private abbrev E3 := EuclideanSpace Real (Fin 3)
private abbrev S1 := sphere (0 : E2) 1

def tangentPlanarLatitude (t : Real) (q : E2) : E3 :=
  vector (Real.sqrt (1 - t ^ 2) * q 0) (Real.sqrt (1 - t ^ 2) * q 1) t

def tangentPlanarMap (z : Real × E2) : E2 :=
  horizontal (tangentFlatShear (tangentPlanarLatitude z.1 z.2))

def tangentPlanarInverse (z : Real × E2) : E2 :=
  WithLp.toLp 2 ![(z.2 0 + tangentFlattenDepth (vector 0 (z.2 1) z.1)) /
    Real.sqrt (1 - z.1 ^ 2), z.2 1 / Real.sqrt (1 - z.1 ^ 2)]

@[simp] theorem tangentPlanarMap_zero (t : Real) (q : E2) :
    tangentPlanarMap (t, q) 0 = Real.sqrt (1 - t ^ 2) * q 0 -
      tangentFlattenDepth (tangentPlanarLatitude t q) := tangentFlatShear_zero _

@[simp] theorem tangentPlanarMap_one (t : Real) (q : E2) :
    tangentPlanarMap (t, q) 1 = Real.sqrt (1 - t ^ 2) * q 1 := tangentFlatShear_one _

theorem contDiffOn_tangentPlanarLatitude :
    ContDiffOn Real ∞ (fun z : Real × E2 => tangentPlanarLatitude z.1 z.2)
      (Ioo (-1 : Real) 1 ×ˢ univ) := by
  have hr : ContDiffOn Real ∞ (fun z : Real × E2 => Real.sqrt (1 - z.1 ^ 2))
      (Ioo (-1 : Real) 1 ×ˢ univ) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contDiffOn.sqrt
      (fun _ hz => (sphereLatitude_radicand_pos hz.1).ne')
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact hr.mul (by fun_prop)
  · exact hr.mul (by fun_prop)
  · exact contDiff_fst.contDiffOn

theorem contDiffOn_tangentPlanarMap :
    ContDiffOn Real ∞ tangentPlanarMap (Ioo (-1 : Real) 1 ×ˢ univ) := by
  exact horizontal_contDiff.comp_contDiffOn
    ((contDiff_id.sub (contDiff_tangentFlattenDepth.smul contDiff_const)).comp_contDiffOn
      contDiffOn_tangentPlanarLatitude)

theorem contDiffOn_tangentPlanarInverse :
    ContDiffOn Real ∞ tangentPlanarInverse (Ioo (-1 : Real) 1 ×ˢ univ) := by
  have hr : ContDiffOn Real ∞ (fun z : Real × E2 => Real.sqrt (1 - z.1 ^ 2))
      (Ioo (-1 : Real) 1 ×ˢ univ) :=
    (contDiff_const.sub (contDiff_fst.pow 2)).contDiffOn.sqrt
      (fun _ hz => (sphereLatitude_radicand_pos hz.1).ne')
  have he : ContDiff Real ∞ (fun z : Real × E2 => vector 0 (z.2 1) z.1) := by
    apply (contDiff_piLp 2).mpr
    intro i
    fin_cases i
    · exact contDiff_const
    · exact (EuclideanSpace.proj (𝕜 := Real) (1 : Fin 2)).contDiff.comp contDiff_snd
    · exact contDiff_fst
  have hn (z : Real × E2) (hz : z ∈ Ioo (-1 : Real) 1 ×ˢ univ) :
      Real.sqrt (1 - z.1 ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos hz.1)).ne'
  apply (contDiffOn_piLp 2).mpr
  intro i
  fin_cases i
  · exact ((by fun_prop : ContDiffOn Real ∞ (fun z : Real × E2 => z.2 0) _).add
      (contDiff_tangentFlattenDepth.comp he).contDiffOn).div hr hn
  · exact (by fun_prop : ContDiffOn Real ∞ (fun z : Real × E2 => z.2 1) _).div hr hn


def tangentPlanarDiffeomorph (t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    Diffeomorph (𝓡 2) (𝓡 2) E2 E2 ∞ where
  toFun q := tangentPlanarMap (t, q)
  invFun q := tangentPlanarInverse (t, q)
  left_inv q := by
    have hr : Real.sqrt (1 - t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)).ne'
    have hd : tangentFlattenDepth (vector 0 (tangentPlanarMap (t, q) 1) t) =
        tangentFlattenDepth (tangentPlanarLatitude t q) := by
      simp [tangentFlattenDepth, tangentRadiusSq, tangentPlanarLatitude]
    ext i
    fin_cases i
    · change (tangentPlanarMap (t, q) 0 +
        tangentFlattenDepth (vector 0 (tangentPlanarMap (t, q) 1) t)) /
          Real.sqrt (1 - t ^ 2) = q 0
      rw [hd, tangentPlanarMap_zero]
      field_simp
      ring
    · change tangentPlanarMap (t, q) 1 / Real.sqrt (1 - t ^ 2) = q 1
      rw [tangentPlanarMap_one]
      exact mul_div_cancel_left₀ _ hr
  right_inv q := by
    have hr : Real.sqrt (1 - t ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)).ne'
    have hq1 : Real.sqrt (1 - t ^ 2) * tangentPlanarInverse (t, q) 1 = q 1 := by
      change Real.sqrt (1 - t ^ 2) * (q 1 / Real.sqrt (1 - t ^ 2)) = q 1
      field_simp
    have hd : tangentFlattenDepth (tangentPlanarLatitude t (tangentPlanarInverse (t, q))) =
        tangentFlattenDepth (vector 0 (q 1) t) := by
      simp only [tangentFlattenDepth, tangentRadiusSq, tangentPlanarLatitude,
        vector_one, vector_two, hq1]
    ext i
    fin_cases i
    · change tangentPlanarMap (t, tangentPlanarInverse (t, q)) 0 = q 0
      rw [tangentPlanarMap_zero, hd]
      change Real.sqrt (1 - t ^ 2) *
        ((q 0 + tangentFlattenDepth (vector 0 (q 1) t)) / Real.sqrt (1 - t ^ 2)) -
          tangentFlattenDepth (vector 0 (q 1) t) = q 0
      field_simp
      ring
    · change tangentPlanarMap (t, tangentPlanarInverse (t, q)) 1 = q 1
      rw [tangentPlanarMap_one]
      exact hq1
  contMDiff_toFun := by
    apply ContDiff.contMDiff
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (contDiffOn_tangentPlanarMap.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ q⟩)).comp q
        ((contDiff_const.prodMk contDiff_id).contDiffAt)
  contMDiff_invFun := by
    apply ContDiff.contMDiff
    apply contDiff_iff_contDiffAt.mpr
    intro q
    exact (contDiffOn_tangentPlanarInverse.contDiffAt
      ((isOpen_Ioo.prod isOpen_univ).mem_nhds ⟨ht, mem_univ q⟩)).comp q
        ((contDiff_const.prodMk contDiff_id).contDiffAt)

theorem tangentPlanarDiffeomorph_sphere (t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    tangentPlanarDiffeomorph t ht '' sphere (0 : E2) 1 =
      range (fun q : S1 => horizontal (tangentFlatShearSlice (t, q))) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨⟨q, hq⟩, rfl⟩
  · rintro ⟨q, rfl⟩
    exact ⟨q, q.property, rfl⟩

theorem tangentPlanarLatitude_image_closedBall {t : Real} (ht : t ∈ Ioo (-1 : Real) 1) :
    tangentPlanarLatitude t '' closedBall (0 : E2) 1 =
      closedBall (0 : E3) 1 ∩ {y | y 2 = t} := by
  let r := Real.sqrt (1 - t ^ 2)
  have hr : 0 < r := Real.sqrt_pos.mpr (sphereLatitude_radicand_pos ht)
  have hrsq : r ^ 2 = 1 - t ^ 2 := Real.sq_sqrt (sphereLatitude_radicand_pos ht).le
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨?_, rfl⟩
    have hqnorm : ‖q‖ ^ 2 ≤ 1 := by
      have h := mem_closedBall_zero_iff.mp hq
      nlinarith [norm_nonneg q]
    have hn : ‖tangentPlanarLatitude t q‖ ^ 2 = r ^ 2 * ‖q‖ ^ 2 + t ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, norm_sq_two]
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs,
        tangentPlanarLatitude, vector_zero, vector_one, vector_two]
      dsimp [r]
      ring
    have hm := mul_le_mul_of_nonneg_left hqnorm (sq_nonneg r)
    rw [mem_closedBall_zero_iff]
    nlinarith [norm_nonneg (tangentPlanarLatitude t q)]
  · rintro ⟨hy, hyt⟩
    change y 2 = t at hyt
    have hyq : y 0 ^ 2 + y 1 ^ 2 ≤ r ^ 2 := by
      have hn := EuclideanSpace.norm_sq_eq y
      have hy' := mem_closedBall_zero_iff.mp hy
      simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs, hyt] at hn
      nlinarith [norm_nonneg y]
    let q : E2 := r⁻¹ • horizontal y
    have hq : q ∈ closedBall (0 : E2) 1 := by
      have hn : ‖q‖ ^ 2 = r⁻¹ ^ 2 * (y 0 ^ 2 + y 1 ^ 2) := by
        rw [norm_sq_two]
        change (r⁻¹ * y 0) ^ 2 + (r⁻¹ * y 1) ^ 2 = _
        ring
      have hm := mul_le_mul_of_nonneg_left hyq (sq_nonneg r⁻¹)
      rw [← hn, inv_pow, inv_mul_cancel₀ (pow_ne_zero 2 hr.ne')] at hm
      rw [mem_closedBall_zero_iff]
      nlinarith [norm_nonneg q]
    refine ⟨q, hq, ?_⟩
    ext i
    fin_cases i
    · change r * (r⁻¹ * y 0) = y 0
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    · change r * (r⁻¹ * y 1) = y 1
      rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul]
    · exact hyt.symm

theorem tangentPlanarDiffeomorph_closedBall (t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    tangentPlanarDiffeomorph t ht '' closedBall (0 : E2) 1 =
      horizontal '' ((tangentFlatShear '' closedBall (0 : E3) 1) ∩ {y | y 2 = t}) := by
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    refine ⟨tangentFlatShear (tangentPlanarLatitude t q), ⟨?_, ?_⟩, rfl⟩
    · exact ⟨tangentPlanarLatitude t q,
        ((tangentPlanarLatitude_image_closedBall ht) ▸ mem_image_of_mem _ hq).1, rfl⟩
    · simp [tangentPlanarLatitude]
  · rintro ⟨p, ⟨⟨x, hx, rfl⟩, hxt⟩, rfl⟩
    have hh : x 2 = t := by
      change tangentFlatShear x 2 = t at hxt
      simpa only [tangentFlatShear_two] using hxt
    obtain ⟨q, hq, hqe⟩ := (tangentPlanarLatitude_image_closedBall ht).symm ▸
      (show x ∈ closedBall (0 : E3) 1 ∩ {y | y 2 = t} from ⟨hx, hh⟩)
    exact ⟨q, hq, congrArg (horizontal ∘ tangentFlatShear) hqe⟩

theorem mem_tangentPlanarDiffeomorph_closedBall_iff {t : Real}
    (ht : t ∈ Ioo (-1 : Real) 1) (y : E2) :
    y ∈ tangentPlanarDiffeomorph t ht '' closedBall (0 : E2) 1 ↔
      vector (y 0) (y 1) t ∈ tangentFlatShear '' closedBall (0 : E3) 1 := by
  rw [tangentPlanarDiffeomorph_closedBall]
  constructor
  · rintro ⟨p, ⟨hp, hpt⟩, hpy⟩
    have he : vector (y 0) (y 1) t = p := by
      rw [← hpy]
      ext i
      fin_cases i
      · rfl
      · rfl
      · exact hpt.symm
    exact he ▸ hp
  · intro hy
    exact ⟨vector (y 0) (y 1) t, ⟨hy, rfl⟩, by ext i; fin_cases i <;> rfl⟩

theorem tangentPlanarDiffeomorph_body_nonpos {t : Real} (ht : t ∈ Ioo (-1 : Real) 1)
    {y : E2} (hy : y ∈ tangentPlanarDiffeomorph t ht '' closedBall (0 : E2) 1) :
    y 0 ≤ 0 :=
  tangentFlatShear_body_nonpos ((mem_tangentPlanarDiffeomorph_closedBall_iff ht y).mp hy)

theorem tangentPlanarDiffeomorph_body_inter_wall (t : Real) (ht : t ∈ Ioo (-1 : Real) 1) :
    (tangentPlanarDiffeomorph t ht '' closedBall (0 : E2) 1) ∩ {y : E2 | y 0 = 0} =
      {y : E2 | y 0 = 0 ∧ (y 1) ^ 2 + t ^ 2 ≤ 1 / 4} := by
  ext y
  constructor
  · rintro ⟨hy, hy0⟩
    have hm : vector (y 0) (y 1) t ∈
        (tangentFlatShear '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} :=
      ⟨(mem_tangentPlanarDiffeomorph_closedBall_iff ht y).mp hy, hy0⟩
    have he : vector (y 0) (y 1) t ∈
        {p : E3 | p 0 = 0 ∧ tangentRadiusSq p ≤ 1 / 4} :=
      tangentFlatShear_body_inter_wall ▸ hm
    exact he
  · intro hy
    have hm : vector (y 0) (y 1) t ∈
        (tangentFlatShear '' closedBall (0 : E3) 1) ∩ {p : E3 | p 0 = 0} :=
      tangentFlatShear_body_inter_wall.symm ▸ hy
    exact ⟨(mem_tangentPlanarDiffeomorph_closedBall_iff ht y).mpr hm.1, hy.1⟩

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Split
