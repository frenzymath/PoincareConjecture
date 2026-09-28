import PoincareConjecture.Proofs.M09.EndpointComparisonAction
import Mathlib.Topology.Order.Compact








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle Topology BigOperators
open Filter

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]

theorem exists_local_minimizing_action_bound {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p : M) (z : M × ℝ)
    (hz : z.2 ∈ Set.Ioo 0 τmax) :
    ∃ (N : Set (M × ℝ)) (D : ℝ), IsOpen N ∧ z ∈ N ∧
      ∀ w ∈ N, ∀ P : BackwardTimePath F T 0 w.2,
        P.curve 0 = p → P.curve w.2 = w.1 →
        IsMinimizingBackwardLPath F T 0 w.2 P → backwardLLength F T 0 w.2 P.curve ≤ D := by
  obtain ⟨U, hU, hzU, _, B, hB, _, hpaths⟩ :=
    exists_local_smooth_comparison_action F hM04 T τmax hτmax hwindow hL p z.1 z.2 hz.1 hz.2
  have hc : ContinuousAt B z := hB.continuousOn.continuousAt (hU.mem_nhds hzU)
  have hnear : {w | B w < B z + 1} ∈ 𝓝 z := hc.eventually_lt_const (lt_add_one _)
  obtain ⟨N, hNsub, hN, hzN⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hzU) hnear)
  refine ⟨N, B z + 1, hN, hzN, ?_⟩
  intro w hw P hP0 hPw hPmin
  obtain ⟨Q, hQ0, hQw, hQ⟩ := hpaths w (hNsub hw).1
  have hle := hPmin Q (hQ0.trans hP0.symm) (hQw.trans hPw.symm)
  rw [hQ] at hle
  exact hle.trans (hNsub hw).2.le

theorem exists_compact_minimizing_action_bound {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hL : LGeodesicTheory F T τmax) (p : M)
    (Q : Set (M × ℝ)) (hQ : IsCompact Q) (hQt : Q ⊆ Set.univ ×ˢ Set.Ioo 0 τmax) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ w ∈ Q, ∀ P : BackwardTimePath F T 0 w.2,
      P.curve 0 = p → P.curve w.2 = w.1 →
      IsMinimizingBackwardLPath F T 0 w.2 P → backwardLLength F T 0 w.2 P.curve ≤ D := by
  classical
  have hloc (z : Q) := exists_local_minimizing_action_bound F hM04 T τmax hτmax hwindow
    hL p z.1 (hQt z.2).2
  choose N D hN hzN hbound using hloc
  obtain ⟨s, hs⟩ := hQ.elim_finite_subcover N hN (by
    intro z hz
    exact Set.mem_iUnion.mpr ⟨⟨z, hz⟩, hzN ⟨z, hz⟩⟩)
  refine ⟨∑ z ∈ s, |D z|, Finset.sum_nonneg (fun z _ ↦ abs_nonneg (D z)), ?_⟩
  intro w hw P hP0 hPw hPmin
  obtain ⟨z, hzs, hz⟩ := Set.mem_iUnion₂.mp (hs hw)
  exact (hbound z w hz P hP0 hPw hPmin).trans ((le_abs_self (D z)).trans
    (Finset.single_le_sum (fun i _ ↦ abs_nonneg (D i)) hzs))

end PoincareConjecture.Proofs.M09
