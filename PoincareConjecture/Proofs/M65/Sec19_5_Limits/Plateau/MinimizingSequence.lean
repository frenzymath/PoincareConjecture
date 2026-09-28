import PoincareConjecture.Definitions.Ch18.LoopSpaceWidth
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic












set_option autoImplicit false

open Set Filter
open scoped Topology Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {M : Type u} [TopologicalSpace M] [ChartedSpace LoopAmbient M]
  [IsManifold (𝓡 3) ∞ M]





theorem m65Plateau_minimizingSequence (g : RiemannianMetric 3 M)
    (gamma : C1FreeLoopSpace (M := M)) (hfill : Nonempty (LipschitzSpanningDisk g gamma)) :
    ∃ disks : ℕ → LipschitzSpanningDisk g gamma,
      (∀ n, fillingArea g gamma ≤ (disks n).area ∧
        (disks n).area < fillingArea g gamma + 1 / ((n : ℝ) + 1)) ∧
      Tendsto (fun n => (disks n).area) atTop (𝓝 (fillingArea g gamma)) := by
  classical
  have hne : (range fun D : LipschitzSpanningDisk g gamma => D.area).Nonempty :=
    ⟨hfill.some.area, mem_range_self hfill.some⟩
  have hbelow : BddBelow (range fun D : LipschitzSpanningDisk g gamma => D.area) :=
    ⟨0, by rintro _ ⟨D, rfl⟩; exact D.area_nonnegative⟩
  have hchoose (n : ℕ) : ∃ D : LipschitzSpanningDisk g gamma,
      D.area < fillingArea g gamma + 1 / ((n : ℝ) + 1) := by
    have herr : 0 < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨_, ⟨D, rfl⟩, hD⟩ := exists_lt_of_csInf_lt hne
      (show sInf (range fun D : LipschitzSpanningDisk g gamma => D.area) <
        fillingArea g gamma + 1 / ((n : ℝ) + 1) from lt_add_of_pos_right _ herr)
    exact ⟨D, hD⟩
  choose disks hdisks using hchoose
  have hlow (n : ℕ) : fillingArea g gamma ≤ (disks n).area :=
    csInf_le hbelow (mem_range_self (disks n))
  refine ⟨disks, fun n => ⟨hlow n, hdisks n⟩, ?_⟩
  have hupp : Tendsto (fun n : ℕ => fillingArea g gamma + 1 / ((n : ℝ) + 1)) atTop
      (𝓝 (fillingArea g gamma)) := by
    simpa only [add_zero] using
      (tendsto_const_nhds (x := fillingArea g gamma)).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupp
    hlow (fun n => (hdisks n).le)

end PoincareConjecture
