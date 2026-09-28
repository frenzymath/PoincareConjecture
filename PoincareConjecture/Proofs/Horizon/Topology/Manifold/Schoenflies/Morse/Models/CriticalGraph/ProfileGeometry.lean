import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.CriticalGraph.ProfileInverse
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Hemisphere
import PoincareConjecture.Proofs.Horizon.Geometry.Euclidean.HeightCoordinates

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

namespace Poincare.Manifold.Schoenflies

private abbrev E3 := EuclideanSpace Real (Fin 3)

def quadraticMinimumCapPoint (v : E3) (c r : Real) (x : Hemisphere.Plane v) : E3 :=
  ((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • x : Hemisphere.Plane v) +
    (c + ‖x‖ ^ 2) • v

def quadraticMinimumCap (v : E3) (c r : Real) : Set E3 :=
  quadraticMinimumCapPoint v c r '' closedBall 0 (7 * r / 8)

theorem inner_quadraticMinimumCapPoint {v : E3} (hv : ‖v‖ = 1)
    (c r : Real) (x : Hemisphere.Plane v) :
    inner Real v (quadraticMinimumCapPoint v c r x) = c + ‖x‖ ^ 2 := by
  unfold quadraticMinimumCapPoint
  simp only [inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq, hv, one_pow,
    mul_one, Submodule.mem_orthogonal_singleton_iff_inner_right.mp
      (((Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • x : Hemisphere.Plane v).property),
    zero_add]

theorem projection_quadraticMinimumCapPoint (v : E3) (c r : Real) (x : Hemisphere.Plane v) :
    (Hemisphere.Plane v).orthogonalProjectionOnto (quadraticMinimumCapPoint v c r x) =
      (Real.sqrt (minimumCapDenominator (‖x‖ ^ 2 / r ^ 2)))⁻¹ • x := by
  simp [quadraticMinimumCapPoint]

theorem norm_projection_quadraticMinimumCapPoint_sq (v : E3) (c : Real) {r : Real}
    (hr : 0 < r) (x : Hemisphere.Plane v) :
    ‖(Hemisphere.Plane v).orthogonalProjectionOnto (quadraticMinimumCapPoint v c r x)‖ ^ 2 =
      r ^ 2 * minimumCapSquaredRadius (‖x‖ ^ 2 / r ^ 2) := by
  rw [projection_quadraticMinimumCapPoint, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr (minimumCapDenominator_pos _))), mul_pow, inv_pow,
    Real.sq_sqrt (minimumCapDenominator_pos _).le]
  unfold minimumCapSquaredRadius
  field_simp

private theorem minimumCapSquaredRadius_lt_one {u : Real} (hu : 0 ≤ u) (hu1 : u < 1 / 2) :
    minimumCapSquaredRadius u < 1 := by
  have hlt := strictMonoOn_minimumCapSquaredRadius ⟨hu, hu1.le⟩
    (show (1 / 2 : Real) ∈ Icc (0 : Real) (1 / 2) by norm_num) hu1
  simpa only [minimumCapSquaredRadius_eq_one le_rfl] using hlt

private theorem mem_quadraticMinimumCap_of_radius
    {v : E3} (c : Real) {r u : Real} (hr : 0 < r)
    (hu : u ∈ Icc (0 : Real) (49 / 64))
    (q : Hemisphere.Plane v)
    (hq : ‖q‖ ^ 2 = r ^ 2 * minimumCapSquaredRadius u) :
    (q : E3) + (c + r ^ 2 * u) • v ∈ quadraticMinimumCap v c r := by
  let x : Hemisphere.Plane v := Real.sqrt (minimumCapDenominator u) • q
  have hr2 : r ^ 2 ≠ 0 := (sq_pos_of_pos hr).ne'
  have hxu : ‖x‖ ^ 2 = r ^ 2 * u := by
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.sqrt_pos.mpr (minimumCapDenominator_pos u)),
      mul_pow, Real.sq_sqrt (minimumCapDenominator_pos u).le]
    change minimumCapDenominator u * ‖q‖ ^ 2 = _
    rw [hq]
    unfold minimumCapSquaredRadius
    field_simp [(minimumCapDenominator_pos u).ne']
  have hxu' : ‖x‖ ^ 2 / r ^ 2 = u := by rw [hxu]; field_simp
  refine ⟨x, mem_closedBall_zero_iff.mpr ?_, ?_⟩
  · nlinarith [hu.2, norm_nonneg x, mul_nonneg (sq_nonneg r) (sub_nonneg.mpr hu.2)]
  · unfold quadraticMinimumCapPoint
    rw [hxu', hxu]
    congr 1
    apply congrArg Subtype.val
    change ((Real.sqrt (minimumCapDenominator u))⁻¹ •
      (Real.sqrt (minimumCapDenominator u) • q) : Hemisphere.Plane v) = q
    rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.mpr (minimumCapDenominator_pos u)).ne', one_smul]

theorem mem_quadraticMinimumCap_iff {v : E3} (hv : ‖v‖ = 1)
    (c : Real) {r : Real} (hr : 0 < r) (y : E3) :
    y ∈ quadraticMinimumCap v c r ↔
      (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ < r ∧
        inner Real v y = c + r ^ 2 *
          minimumCapHeight (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ ^ 2 / r ^ 2)) ∨
      (‖(Hemisphere.Plane v).orthogonalProjectionOnto y‖ = r ∧
        inner Real v y ∈ Icc (c + r ^ 2 / 2) (c + (7 * r / 8) ^ 2)) := by
  have hr2 : 0 < r ^ 2 := sq_pos_of_pos hr
  constructor
  · rintro ⟨x, hx, rfl⟩
    let u := ‖x‖ ^ 2 / r ^ 2
    have hu0 : 0 ≤ u := div_nonneg (sq_nonneg _) hr2.le
    have hxu : ‖x‖ ^ 2 = r ^ 2 * u := by dsimp [u]; field_simp
    have hxnorm := mem_closedBall_zero_iff.mp hx
    have hu1 : u ≤ 49 / 64 := by
      apply (div_le_iff₀ hr2).mpr
      nlinarith [norm_nonneg x]
    have hnorm := norm_projection_quadraticMinimumCapPoint_sq v c hr x
    change _ = r ^ 2 * minimumCapSquaredRadius u at hnorm
    by_cases hu : u < 1 / 2
    · have hR := minimumCapSquaredRadius_lt_one hu0 hu
      have hz0 : 0 ≤ minimumCapSquaredRadius u :=
        div_nonneg hu0 (minimumCapDenominator_pos u).le
      have hz : ‖(Hemisphere.Plane v).orthogonalProjectionOnto
          (quadraticMinimumCapPoint v c r x)‖ ^ 2 / r ^ 2 = minimumCapSquaredRadius u := by
        rw [hnorm]
        field_simp
      refine Or.inl ⟨?_, ?_⟩
      · nlinarith [mul_pos hr2 (sub_pos.mpr hR),
          norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto
            (quadraticMinimumCapPoint v c r x))]
      · rw [inner_quadraticMinimumCapPoint hv, hz,
          minimumCapHeight_eq_of_radius hz0 hR ⟨hu0, hu⟩ rfl, hxu]
    · rw [minimumCapSquaredRadius_eq_one (le_of_not_gt hu), mul_one] at hnorm
      refine Or.inr ⟨?_, ?_⟩
      · nlinarith [norm_nonneg ((Hemisphere.Plane v).orthogonalProjectionOnto
          (quadraticMinimumCapPoint v c r x))]
      · rw [inner_quadraticMinimumCapPoint hv, hxu]
        constructor
        · nlinarith [mul_nonneg hr2.le (sub_nonneg.mpr (le_of_not_gt hu))]
        · nlinarith [mul_nonneg hr2.le (sub_nonneg.mpr hu1)]
  · let q := (Hemisphere.Plane v).orthogonalProjectionOnto y
    have hdecomp : (q : E3) + inner Real v y • v = y := by
      rw [add_comm]
      exact (Poincare.Geometry.Euclidean.heightCoordinates hv).apply_symm_apply y
    rintro (⟨hqr, hyheight⟩ | ⟨hqr, hyheight⟩)
    · let z := ‖q‖ ^ 2 / r ^ 2
      have hz0 : 0 ≤ z := div_nonneg (sq_nonneg _) hr2.le
      have hz1 : z < 1 := by
        apply (div_lt_iff₀ hr2).mpr
        have hq0 := norm_nonneg q
        change ‖q‖ < r at hqr
        nlinarith
      let u := minimumCapHeight z
      have hu := (minimumCapHeight_spec hz0 hz1).1
      have huR := (minimumCapHeight_spec hz0 hz1).2
      have hq : ‖q‖ ^ 2 = r ^ 2 * minimumCapSquaredRadius u := by
        rw [huR]
        dsimp [z]
        field_simp
      have hmem := mem_quadraticMinimumCap_of_radius c hr
        (show u ∈ Icc (0 : Real) (49 / 64) from ⟨hu.1, by linarith [hu.2]⟩) q hq
      rwa [← hyheight, hdecomp] at hmem
    · let u := (inner Real v y - c) / r ^ 2
      have hu0 : 1 / 2 ≤ u := (le_div_iff₀ hr2).mpr (by linarith [hyheight.1])
      have hu1 : u ≤ 49 / 64 := (div_le_iff₀ hr2).mpr (by nlinarith [hyheight.2])
      have hyu : c + r ^ 2 * u = inner Real v y := by dsimp [u]; field_simp; ring
      have hq : ‖q‖ ^ 2 = r ^ 2 * minimumCapSquaredRadius u := by
        rw [minimumCapSquaredRadius_eq_one hu0, mul_one]
        change ‖q‖ = r at hqr
        rw [hqr]
      have hmem := mem_quadraticMinimumCap_of_radius c hr ⟨by linarith, hu1⟩ q hq
      rwa [hyu, hdecomp] at hmem

end Poincare.Manifold.Schoenflies
