import PoincareLib.Geometry.CurveShortening.Comparison.AnnularEvolution.Boundary.Regular.ArcFrame

/-! Literal rectangular collars inside the quantitative half disks.
A genuine C1 boundary tangent supplies an interval before selecting
the finite boundary cover; later only the common height is reduced.
Source: MT Lemma 19.15, pp. 447-449; M64 finite collar derivation. -/

noncomputable section
set_option autoImplicit false
set_option warningAsError true

open Set Filter Metric Complex
open scoped Topology ContDiff

namespace PoincareMT.M64

/-- The literal horizontal collar rectangle lies strictly inside the radial ball when twice
its width is less than the radius. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
project derivations `proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md`
and `proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem collar_rectangle_norm_lt {e R t h : ℝ} (heR : 2 * e < R)
    (ht : t ∈ Icc (-e) e) (hh : h ∈ Icc (0 : ℝ) e) :
    ‖(t : ℂ) + (h : ℂ) * I‖ < R := by
  have ht' : |t| ≤ e := abs_le.mpr ht
  have hn := norm_add_le (t : ℂ) ((h : ℂ) * I)
  simp only [norm_real, Real.norm_eq_abs, norm_mul, norm_I, mul_one, abs_of_nonneg hh.1] at hn
  linarith [hh.2]

/-- Actual C1 regularity of the boundary tangent chooses a positive closed interval and a
genuine interior rectangular collar. Source: Morgan--Tian (2007), Lemma 19.15, pp. 447-449;
project derivations `proof-work/tasks/M64/derivations/2026-09-26-finite-boundary-collar.md`
and `proof-work/tasks/M64/derivations/2026-09-26-periodic-finite-collar.md`. -/
theorem halfDisk_boundary_collar_width
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T : ℝ → E} {R : ℝ} (hR : 0 < R) (hT : ContDiffAt ℝ 1 T 0) :
    ∃ e : ℝ, 0 < e ∧ 2 * e < R ∧ ∀ t ∈ Icc (-e) e, ContDiffAt ℝ 1 T t := by
  obtain ⟨d, hd, hsub⟩ := nhds_basis_closedBall.mem_iff.mp (hT.eventually (by norm_num))
  let e := min (R / 4) (d / 2)
  have he : 0 < e := lt_min (by positivity) (half_pos hd)
  refine ⟨e, he, ?_, ?_⟩
  · have h := min_le_left (R / 4) (d / 2)
    dsimp only [e]
    linarith
  · intro t ht
    apply hsub
    rw [mem_closedBall_zero_iff, Real.norm_eq_abs]
    exact (abs_le.mpr ht).trans ((min_le_right _ _).trans (by linarith))

end PoincareMT.M64
