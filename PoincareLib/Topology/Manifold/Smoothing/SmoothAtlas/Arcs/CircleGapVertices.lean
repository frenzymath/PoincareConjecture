import PoincareLib.Topology.Manifold.Smoothing.SmoothAtlas.Arcs.CircleGapConfigurations
import Mathlib.Topology.Instances.AddCircle.Real

/-!
# Circle vertices recovered from angular gaps

Prefix sums of positive cyclic gaps give distinct, continuously varying
vertices of the additive circle, with the first marked edge fixed. This is
the angular-coordinate step for Cairns 1940, Section 6, p. 802, and
Lemma 11.1, p. 807, footnote 14. See M76 derivation 13.
-/

set_option autoImplicit false

open Set

namespace PoincareMT.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

/-- The real angle of a vertex is the sum of preceding cyclic gaps.
See Cairns p. 802 and M76 derivation 13. -/
def gapAngle (w : Fin (n + 3) → ℝ) (i : Fin (n + 3)) : ℝ :=
  ∑ j ∈ Finset.Iio i, w j

/-- The first vertex is at angle zero. See M76 derivation 13. -/
@[simp] theorem gapAngle_zero (w : Fin (n + 3) → ℝ) : gapAngle w 0 = 0 := by
  change (∑ j ∈ Finset.Iio (⊥ : Fin (n + 3)), w j) = 0
  rw [Finset.Iio_bot, Finset.sum_empty]

/-- Consecutive lifted angles differ by their intervening gap.
See Cairns p. 802 and M76 derivation 13. -/
theorem gapAngle_succ (w : Fin (n + 3) → ℝ) (i : Fin (n + 2)) :
    gapAngle w i.succ = gapAngle w i.castSucc + w i.castSucc := by
  have hset : Finset.Iio i.succ = insert i.castSucc (Finset.Iio i.castSucc) := by
    ext j
    simp only [Finset.mem_Iio, Finset.mem_insert, Fin.lt_def,
      Fin.val_succ, Fin.val_castSucc, Fin.ext_iff]
    omega
  simp only [gapAngle]
  rw [hset, Finset.sum_insert (by simp)]
  exact add_comm _ _

/-- Positive gaps give strictly ordered lifted vertex angles.
See Cairns p. 802 and M76 derivation 13. -/
theorem strictMono_gapAngle {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    StrictMono (gapAngle w) := by
  intro i j hij
  apply Finset.sum_lt_sum_of_subset
    (fun k hk => Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij))
    (Finset.mem_Iio.mpr hij) (by simp) (hw.1 i).1
  intro k _ _
  exact (hw.1 k).1.le

/-- Every lifted vertex angle lies in one fundamental interval, with a
strict upper bound even at the final vertex. See M76 derivation 13. -/
theorem gapAngle_mem_Ico {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta)
    (i : Fin (n + 3)) : gapAngle w i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  refine ⟨Finset.sum_nonneg (fun j _ => (hw.1 j).1.le), ?_⟩
  calc
    gapAngle w i < ∑ j, w j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i)
        (by simp) (hw.1 i).1 (fun j _ _ => (hw.1 j).1.le)
    _ = 2 * Real.pi := hw.2.1

/-- The second marked vertex is at the prescribed angle.
See Cairns p. 802 and M76 derivation 13. -/
theorem gapAngle_one {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    gapAngle w 1 = theta := by
  have h := gapAngle_succ w (0 : Fin (n + 2))
  simpa [hw.2.2] using h

/-- Lifted vertex angles depend continuously on the gap coordinates.
See M76 derivation 13. -/
theorem continuous_gapAngle (i : Fin (n + 3)) :
    Continuous (fun w : Fin (n + 3) → ℝ => gapAngle w i) :=
  continuous_finsetSum _ fun j _ => continuous_apply j

/-- The cyclic vertices in the circle of circumference two pi.
See Cairns p. 802 and M76 derivation 13. -/
noncomputable def circleGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    AddCircle (2 * Real.pi) := (gapAngle w i : AddCircle (2 * Real.pi))

/-- The recovered circle vertices are pairwise distinct. Reduction modulo
two pi cannot identify two lifted angles in the fundamental interval.
See M76 derivation 13. -/
theorem injective_circleGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (circleGapVertices w) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply (strictMono_gapAngle w.property).injective
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
    (by simpa using gapAngle_mem_Ico w.property i)
    (by simpa using gapAngle_mem_Ico w.property j)).mp hij

/-- The circle vertices move continuously with the angular-gap parameters.
See Cairns p. 802 and M76 derivation 13. -/
theorem continuous_circleGapVertices :
    Continuous (circleGapVertices : shortArcGapSpace n theta → Fin (n + 3) →
      AddCircle (2 * Real.pi)) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
    ((continuous_gapAngle i).comp continuous_subtype_val)

end PoincareMT.M76.Smoothing
