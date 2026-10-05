import PoincareLib.Topology.Manifold.Smoothing.Schoenflies.Coordinates.PolarRadiusCoordinates

/-!
# Exact polar fibers and the literal unit ball and sphere

The regular inverse identifies every non-endpoint fiber. Direct norm
algebra identifies the entire equator and closed lower half with the
literal unit sphere and closed unit ball in the finite chart.
See Brown1960 Theorem5 and Brown derivation018, sections3--4.
-/

set_option autoImplicit false

open Set Metric
open scoped OnePoint

namespace BrownSchoenflies

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The full upper endpoint face is exactly the fiber over infinity. -/
theorem compactifiedPolar_eq_infty_iff (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    compactifiedPolar z = ∞ ↔ (z.2 : ℝ) = 1 := by
  by_cases hz : (z.2 : ℝ) = 1 <;> simp [compactifiedPolar, hz]

/-- The full lower endpoint face is exactly the fiber over the finite origin. -/
theorem compactifiedPolar_eq_zero_iff (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    compactifiedPolar z = ((0 : E) : OnePoint E) ↔ (z.2 : ℝ) = -1 := by
  by_cases hz : (z.2 : ℝ) = 1
  · norm_num [compactifiedPolar, hz]
  · have hzt : (z.2 : ℝ) < 1 := lt_of_le_of_ne z.2.property.2 hz
    rw [compactifiedPolar, if_neg hz, OnePoint.coe_eq_coe, ← norm_eq_zero,
      norm_polarVector z hzt, polarRadius, div_eq_iff (sub_pos.mpr hzt).ne']
    constructor <;> intro h <;> linarith

/-- Exact membership in the finite unit sphere holds precisely on
the full height-zero face. See Brown derivation018, section3. -/
theorem compactifiedPolar_mem_sphere_iff (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    compactifiedPolar z ∈ ((↑) : E → OnePoint E) '' sphere (0 : E) 1 ↔
      (z.2 : ℝ) = 0 := by
  by_cases hz : (z.2 : ℝ) = 1
  · simp only [compactifiedPolar, hz, if_true, OnePoint.infty_notMem_image_coe]
    norm_num
  · have hzt : (z.2 : ℝ) < 1 := lt_of_le_of_ne z.2.property.2 hz
    rw [compactifiedPolar, if_neg hz, OnePoint.coe_injective.mem_set_image,
      mem_sphere_zero_iff_norm, norm_polarVector z hzt,
      polarRadius, div_eq_iff (sub_pos.mpr hzt).ne']
    constructor <;> intro h <;> linarith

/-- Exact membership in the finite closed unit ball holds precisely
on the full lower half, including the negative endpoint face.
See Brown derivation018, section3. -/
theorem compactifiedPolar_mem_closedBall_iff (z : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    compactifiedPolar z ∈ ((↑) : E → OnePoint E) '' closedBall (0 : E) 1 ↔
      (z.2 : ℝ) ≤ 0 := by
  by_cases hz : (z.2 : ℝ) = 1
  · simp only [compactifiedPolar, hz, if_true, OnePoint.infty_notMem_image_coe]
    norm_num
  · have hzt : (z.2 : ℝ) < 1 := lt_of_le_of_ne z.2.property.2 hz
    rw [compactifiedPolar, if_neg hz, OnePoint.coe_injective.mem_set_image,
      mem_closedBall_zero_iff, norm_polarVector z hzt,
      polarRadius, div_le_iff₀ (sub_pos.mpr hzt)]
    constructor <;> intro h <;> linarith

/-- The constructed map has precisely the two complete endpoint
faces as exceptional fibers. See Brown derivation018, section3. -/
theorem compactifiedPolar_fibers (z w : sphere (0 : E) 1 × Icc (-1 : ℝ) 1) :
    compactifiedPolar z = compactifiedPolar w ↔ z = w ∨
      ((z.2 : ℝ) = -1 ∧ (w.2 : ℝ) = -1) ∨
      ((z.2 : ℝ) = 1 ∧ (w.2 : ℝ) = 1) := by
  constructor
  · intro hzw
    by_cases hz1 : (z.2 : ℝ) = 1
    · exact Or.inr (Or.inr ⟨hz1, (compactifiedPolar_eq_infty_iff w).mp
        (hzw.symm.trans ((compactifiedPolar_eq_infty_iff z).mpr hz1))⟩)
    by_cases hzm : (z.2 : ℝ) = -1
    · exact Or.inr (Or.inl ⟨hzm, (compactifiedPolar_eq_zero_iff w).mp
        (hzw.symm.trans ((compactifiedPolar_eq_zero_iff z).mpr hzm))⟩)
    have hw1 : (w.2 : ℝ) ≠ 1 := fun h => hz1 ((compactifiedPolar_eq_infty_iff z).mp
      (hzw.trans ((compactifiedPolar_eq_infty_iff w).mpr h)))
    have hwm : (w.2 : ℝ) ≠ -1 := fun h => hzm ((compactifiedPolar_eq_zero_iff z).mp
      (hzw.trans ((compactifiedPolar_eq_zero_iff w).mpr h)))
    let zi : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1 :=
      (z.1, ⟨z.2.val, lt_of_le_of_ne z.2.property.1 (Ne.symm hzm),
        lt_of_le_of_ne z.2.property.2 hz1⟩)
    let wi : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1 :=
      (w.1, ⟨w.2.val, lt_of_le_of_ne w.2.property.1 (Ne.symm hwm),
        lt_of_le_of_ne w.2.property.2 hw1⟩)
    have he : ((regularPolarHomeomorph zi : E) : OnePoint E) =
        ((regularPolarHomeomorph wi : E) : OnePoint E) :=
      (compactifiedPolar_regular zi).symm.trans (hzw.trans (compactifiedPolar_regular wi))
    have hzi : zi = wi := regularPolarHomeomorph.injective
      (Subtype.ext (OnePoint.coe_injective he))
    exact Or.inl (Prod.ext (congrArg (fun v : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1 => v.1) hzi)
      (Subtype.ext (congrArg (fun v : sphere (0 : E) 1 × Ioo (-1 : ℝ) 1 => (v.2 : ℝ)) hzi)))
  · rintro (rfl | ⟨hz, hw⟩ | ⟨hz, hw⟩)
    · rfl
    · exact ((compactifiedPolar_eq_zero_iff z).mpr hz).trans
        ((compactifiedPolar_eq_zero_iff w).mpr hw).symm
    · exact ((compactifiedPolar_eq_infty_iff z).mpr hz).trans
        ((compactifiedPolar_eq_infty_iff w).mpr hw).symm

/-- Every point of the actual compactification occurs as a polar
value, including both poles. See Brown derivation018, section3. -/
theorem compactifiedPolar_surjective [Nonempty (sphere (0 : E) 1)] :
    Function.Surjective (compactifiedPolar (E := E)) := by
  classical
  let u : sphere (0 : E) 1 := Classical.choice inferInstance
  intro y
  induction y using OnePoint.rec with
  | infty =>
      exact ⟨(u, ⟨1, by constructor <;> norm_num⟩),
        (compactifiedPolar_eq_infty_iff _).mpr rfl⟩
  | coe y =>
      by_cases hy : y = 0
      · subst y
        exact ⟨(u, ⟨-1, by constructor <;> norm_num⟩),
          (compactifiedPolar_eq_zero_iff _).mpr rfl⟩
      · let v : ↥(({0} : Set E)ᶜ) := ⟨y, hy⟩
        let z := regularPolarHomeomorph.symm v
        refine ⟨(z.1, ⟨z.2.val, z.2.property.1.le, z.2.property.2.le⟩), ?_⟩
        rw [compactifiedPolar_regular]
        exact congrArg (fun x : ↥(({0} : Set E)ᶜ) => ((x : E) : OnePoint E))
          (regularPolarHomeomorph.apply_symm_apply v)

end BrownSchoenflies
