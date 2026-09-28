import PoincareConjecture.Proofs.M09.EndpointComparisonAction
import PoincareConjecture.Proofs.M09.PathComparison
import Mathlib.Topology.Semicontinuity.Basic

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem reducedLength_upperSemicontinuousAt {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p : M) (z : M × ℝ)
    (hz : z.2 ∈ Set.Ioo 0 τmax) :
    UpperSemicontinuousAt (fun w : M × ℝ ↦ reducedLength F T p w.1 w.2) z := by
  obtain ⟨N, hN, hzN, hNt, B, hB, hBz, hpaths⟩ :=
    exists_local_smooth_comparison_action F hM04 T τmax hτmax hwindow hL p z.1 z.2 hz.1 hz.2
  let C : M × ℝ → ℝ := fun w ↦ B w / (2 * Real.sqrt w.2)
  have hden : 2 * Real.sqrt z.2 ≠ 0 := (mul_pos zero_lt_two (Real.sqrt_pos.mpr hz.1)).ne'
  have hC : ContinuousAt C z :=
    (hB.continuousOn.continuousAt (hN.mem_nhds hzN)).div
      (continuousAt_const.mul (Real.continuous_sqrt.continuousAt.comp continuousAt_snd)) hden
  have hCz : C z = reducedLength F T p z.1 z.2 := by
    dsimp only [C]
    rw [hBz, mul_div_cancel_left₀ _ hden]
  intro a ha
  have hCa : C z < a := hCz ▸ ha
  filter_upwards [hN.mem_nhds hzN, hC.eventually_lt_const hCa] with w hw hwa
  obtain ⟨P, hP0, hPw, hPaction⟩ := hpaths w hw
  have hle := reducedLength_le_path hL (hNt hw).2.1 (hNt hw).2.2.le P hP0 hPw
  rw [hPaction] at hle
  exact hle.trans_lt hwa

theorem reducedLength_upperSemicontinuousOn {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p : M) :
    UpperSemicontinuousOn (fun w : M × ℝ ↦ reducedLength F T p w.1 w.2)
      (Set.univ ×ˢ Set.Ioo 0 τmax) := by
  intro z hz
  exact (reducedLength_upperSemicontinuousAt F hM04 T τmax hτmax hwindow hL p z hz.2).upperSemicontinuousWithinAt _

end PoincareConjecture.Proofs.M09
