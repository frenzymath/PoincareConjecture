import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Graphs.PlanarCycleGaps

/-!
# Global gap coordinates of normalized radial cycles

The positive short increments of a normalized unit radial cycle add to
one full turn and reconstruct every vertex. Thus the geometry forces
the cyclic order used in gap coordinates. See Cairns 1940, Section 6,
p. 802 and Section 11, p. 807, footnote 14; M76 derivation 23.
-/

set_option autoImplicit false

open Set NormedSpace

namespace PoincareMT.M76.Smoothing

variable {n : ℕ}

/-- Exponentiating prefix sums of the recovered increments reconstructs
each original vertex. See Cairns p. 802 and M76 derivation 23. -/
theorem exp_gapAngle_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (hzero : unitCycleVertex v 0 = 1) (i : Fin (n + 3)) :
    Circle.exp (gapAngle (cycleIncrement v) i) = unitCycleVertex v i := by
  induction i using Fin.induction with
  | zero => rw [gapAngle_zero, Circle.exp_zero, hzero]
  | succ i ih =>
      rw [gapAngle_succ, Circle.exp_add, ih]
      simpa only [cycleIncrement, Fin.coeSucc_eq_succ] using
        Circle.mul_exp_shortIncrement (unitCycleVertex v i.castSucc)
          (unitCycleVertex v (i.castSucc + 1))

/-- The closing edge makes the total increment an integer number of
full turns. See Cairns p. 802 and M76 derivation 23. -/
theorem exp_sum_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ)
    (hzero : unitCycleVertex v 0 = 1) : Circle.exp (∑ i, cycleIncrement v i) = 1 := by
  rw [← gapAngle_last_add, Circle.exp_add, exp_gapAngle_cycleIncrement v hzero]
  simpa only [cycleIncrement, Fin.last_add_one, hzero] using
    Circle.mul_exp_shortIncrement (unitCycleVertex v (Fin.last (n + 2)))
      (unitCycleVertex v (Fin.last (n + 2) + 1))

/-- No nonclosing edge can complete a full turn: that would put the
marked origin vertex on a nonincident edge.
See Cairns p. 802 and M76 derivation 23. -/
theorem gapAngle_cycleIncrement_lt_fullTurn
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta)
    (i : Fin (n + 3)) : gapAngle (cycleIncrement v) i < 2 * Real.pi := by
  induction i using Fin.induction with
  | zero => rw [gapAngle_zero]; positivity
  | succ i ih =>
      by_cases hi0 : i.castSucc = 0
      · rw [gapAngle_succ, hi0, gapAngle_zero, zero_add]
        linarith [(cycleIncrement_mem_Ioo v 0).2, Real.pi_pos]
      · by_contra hlt
        have hhigh := le_of_not_gt hlt
        have hgap : gapAngle (cycleIncrement v) i.succ -
            gapAngle (cycleIncrement v) i.castSucc = cycleIncrement v i.castSucc := by
          rw [gapAngle_succ]
          ring
        have hpos : gapAngle (cycleIncrement v) i.castSucc <
            gapAngle (cycleIncrement v) i.succ := by
          have hp := cycleIncrement_pos v htheta hzero hone i.castSucc
          linarith
        have hshort : gapAngle (cycleIncrement v) i.succ -
            gapAngle (cycleIncrement v) i.castSucc < Real.pi := by
          rw [hgap]
          exact (cycleIncrement_mem_Ioo v i.castSucc).2
        have hmem : (Circle.exp (2 * Real.pi) : ℂ) ∈ NormedSpace.normalize ''
            segment ℝ (Circle.exp (gapAngle (cycleIncrement v) i.castSucc) : ℂ)
              (Circle.exp (gapAngle (cycleIncrement v) i.succ)) := by
          rw [Complex.normalize_image_segment_circleExp hpos hshort]
          exact ⟨2 * Real.pi, ⟨ih.le, hhigh⟩, rfl⟩
        rw [Circle.exp_two_pi, exp_gapAngle_cycleIncrement v hzero,
          exp_gapAngle_cycleIncrement v hzero] at hmem
        have hends := (unitCycleVertex_mem_normalize_edge_iff v i.castSucc 0).mp
          (by simpa only [Fin.coeSucc_eq_succ, hzero] using hmem)
        rcases hends with he | he
        · exact hi0 he.symm
        · exact Fin.succ_ne_zero i (by simpa only [Fin.coeSucc_eq_succ] using he.symm)

/-- The recovered positive angular increments sum to exactly one turn,
not a larger winding number. See Cairns p. 802 and M76 derivation 23. -/
theorem sum_cycleIncrement (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    (∑ i, cycleIncrement v i) = 2 * Real.pi := by
  have hpositive : 0 < ∑ i, cycleIncrement v i :=
    Finset.sum_pos (fun i _ => cycleIncrement_pos v htheta hzero hone i) Finset.univ_nonempty
  have hbound : (∑ i, cycleIncrement v i) < 3 * Real.pi := by
    have hlast := gapAngle_cycleIncrement_lt_fullTurn v htheta hzero hone (Fin.last (n + 2))
    have hgap := (cycleIncrement_mem_Ioo v (Fin.last (n + 2))).2
    linarith [gapAngle_last_add (cycleIncrement v)]
  obtain ⟨m, hm⟩ := Circle.exp_eq_one.mp (exp_sum_cycleIncrement v hzero)
  have hmpos : (0 : ℝ) < m := by nlinarith [Real.pi_pos]
  have hmlt : (m : ℝ) < 2 := by nlinarith [Real.pi_pos]
  have hmpos' : (0 : ℤ) < m := by exact_mod_cast hmpos
  have hmlt' : m < (2 : ℤ) := by exact_mod_cast hmlt
  have hmone : m = 1 := by omega
  simpa only [hmone, Int.cast_one, one_mul] using hm

/-- A normalized unit radial realization yields valid short-gap
coordinates, with positivity and cyclic order derived from its geometry.
See Cairns pp. 802, 807 and M76 derivation 23. -/
theorem cycleIncrement_mem_shortArcGapSpace
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    cycleIncrement v ∈ shortArcGapSpace n theta :=
  ⟨fun i => ⟨cycleIncrement_pos v htheta hzero hone i, (cycleIncrement_mem_Ioo v i).2⟩,
    sum_cycleIncrement v htheta hzero hone, cycleIncrement_zero v htheta hzero hone⟩

/-- Reconstructing the planar vertices from the recovered gaps gives
the original vertex assignment exactly.
See Cairns p. 802 and M76 derivation 23. -/
theorem planarGapVertices_cycleIncrement
    (v : (cyclicEdgeComplex n).UnitRadialEmbedding ℂ) {theta : ℝ}
    (htheta : theta ∈ Ioo (0 : ℝ) Real.pi)
    (hzero : unitCycleVertex v 0 = 1) (hone : unitCycleVertex v 1 = Circle.exp theta) :
    planarGapVertices ⟨cycleIncrement v, cycleIncrement_mem_shortArcGapSpace v htheta hzero hone⟩ =
      v.val.val := by
  funext i
  exact congrArg (fun z : Circle => (z : ℂ)) (exp_gapAngle_cycleIncrement v hzero i)

end PoincareMT.M76.Smoothing
