import PoincareConjecture.Proofs.M76.Smoothing.CircleGapConfigurations
import Mathlib.Topology.Instances.AddCircle.Real

set_option autoImplicit false

open Set

namespace PoincareConjecture.M76.Smoothing

variable {n : ℕ} {theta : ℝ}

def gapAngle (w : Fin (n + 3) → ℝ) (i : Fin (n + 3)) : ℝ :=
  ∑ j ∈ Finset.Iio i, w j

@[simp] theorem gapAngle_zero (w : Fin (n + 3) → ℝ) : gapAngle w 0 = 0 := by
  change (∑ j ∈ Finset.Iio (⊥ : Fin (n + 3)), w j) = 0
  rw [Finset.Iio_bot, Finset.sum_empty]

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

theorem strictMono_gapAngle {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    StrictMono (gapAngle w) := by
  intro i j hij
  apply Finset.sum_lt_sum_of_subset
    (fun k hk => Finset.mem_Iio.mpr ((Finset.mem_Iio.mp hk).trans hij))
    (Finset.mem_Iio.mpr hij) (by simp) (hw.1 i).1
  intro k _ _
  exact (hw.1 k).1.le

theorem gapAngle_mem_Ico {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta)
    (i : Fin (n + 3)) : gapAngle w i ∈ Ico (0 : ℝ) (2 * Real.pi) := by
  refine ⟨Finset.sum_nonneg (fun j _ => (hw.1 j).1.le), ?_⟩
  calc
    gapAngle w i < ∑ j, w j :=
      Finset.sum_lt_sum_of_subset (Finset.subset_univ _) (Finset.mem_univ i)
        (by simp) (hw.1 i).1 (fun j _ _ => (hw.1 j).1.le)
    _ = 2 * Real.pi := hw.2.1

theorem gapAngle_one {w : Fin (n + 3) → ℝ} (hw : w ∈ shortArcGapSpace n theta) :
    gapAngle w 1 = theta := by
  have h := gapAngle_succ w (0 : Fin (n + 2))
  simpa [hw.2.2] using h

theorem continuous_gapAngle (i : Fin (n + 3)) :
    Continuous (fun w : Fin (n + 3) → ℝ => gapAngle w i) :=
  continuous_finsetSum _ fun j _ => continuous_apply j

noncomputable def circleGapVertices (w : shortArcGapSpace n theta) (i : Fin (n + 3)) :
    AddCircle (2 * Real.pi) := (gapAngle w i : AddCircle (2 * Real.pi))

theorem injective_circleGapVertices (w : shortArcGapSpace n theta) :
    Function.Injective (circleGapVertices w) := by
  let : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩
  intro i j hij
  apply (strictMono_gapAngle w.property).injective
  exact (AddCircle.coe_eq_coe_iff_of_mem_Ico (a := 0)
    (by simpa using gapAngle_mem_Ico w.property i)
    (by simpa using gapAngle_mem_Ico w.property j)).mp hij

theorem continuous_circleGapVertices :
    Continuous (circleGapVertices : shortArcGapSpace n theta → Fin (n + 3) →
      AddCircle (2 * Real.pi)) := by
  apply continuous_pi
  intro i
  exact (AddCircle.continuous_mk' (2 * Real.pi)).comp
    ((continuous_gapAngle i).comp continuous_subtype_val)

end PoincareConjecture.M76.Smoothing
