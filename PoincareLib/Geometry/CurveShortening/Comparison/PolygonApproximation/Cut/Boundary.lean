import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Domain.Boundary

/-!
# Nullity of polygon cut lines

The vertical derivative of the interpolator is transported cellwise.  The
cell interfaces form finitely many coordinate lines, so they may be removed
when the resulting bound is stated almost everywhere.

Morgan--Tian context: Section 19.4, Definition 19.18 and Claims 19.19-19.22, printed pp.
450-453.
-/

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal

namespace PoincareMT

/-- A vertical coordinate line has zero planar volume. Source: Auxiliary step for MT
Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_cut_line_null (c : ℝ) :
    volume {p : LoopPlane | p 0 = c} = 0 := by
  let e : LoopPlane → (Fin 2 → ℝ) := @WithLp.ofLp 2 (Fin 2 → ℝ)
  let q : (Fin 2 → ℝ) → ℝ × ℝ := MeasurableEquiv.finTwoArrow
  have he : MeasurePreserving e volume volume := PiLp.volume_preserving_ofLp _
  have hq : MeasurePreserving q volume volume :=
    MeasureTheory.volume_preserving_finTwoArrow ℝ
  have hcomp : MeasurePreserving (q ∘ e) volume volume := hq.comp he
  let S : Set (ℝ × ℝ) := {c} ×ˢ (Set.univ : Set ℝ)
  have hS : NullMeasurableSet S volume := by measurability
  have hzero : volume S = 0 := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod]
    simp
  have hpre := hcomp.measure_preimage hS
  have heq : (q ∘ e) ⁻¹' S = {p : LoopPlane | p 0 = c} := by
    ext p
    simp [q, e, S, MeasurableEquiv.finTwoArrow_apply]
  rw [← heq, hpre, hzero]

/-- The finite union of polygon cut lines has zero planar volume. Source: Auxiliary step for
MT Definition 19.18 and Claims 19.19/19.22, pp. 450-453; project construction in
`proof-work/tasks/M64/reports/2026-09-23-static-polygon.md`. -/
theorem m64_cut_lines_null
    {k : ℕ} (cut : Fin (k + 1) → ℝ) :
    volume {p : LoopPlane | ∃ j : Fin (k + 1), p 0 = cut j} = 0 := by
  let line : Fin (k + 1) → Set LoopPlane :=
    fun j => {p : LoopPlane | p 0 = cut j}
  have hline : ∀ j, volume (line j) = 0 := by
    intro j
    exact m64_cut_line_null (cut j)
  have hu : (⋃ j, line j) = {p : LoopPlane |
      ∃ j : Fin (k + 1), p 0 = cut j} := by
    ext p
    simp [line]
  rw [← hu]
  exact measure_iUnion_null hline

end PoincareMT
