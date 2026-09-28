import PoincareConjecture.Proofs.M09.MinimizerLifts
import PoincareConjecture.Proofs.M09.PathMinimality
import PoincareConjecture.Proofs.M09.PathComparison








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem lExponentialFamily_exists_minimizing_initialVector [T2Space M]
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (b : ℝ) (hb : 0 < b) (hmax : b < τmax) (x : M) :
    ∃ Z : TangentSpace (𝓡 n) p, A.gamma Z b = x ∧
      IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax) := by
  obtain ⟨q, hq0, hqb, hqmin⟩ := hL.minimizing_existence 0 b le_rfl hb hmax.le p x
  obtain ⟨Z, heq, _⟩ := lExponentialFamily_minimizers_lift hM04 hL hτmax hwindow
    A b hb hmax q hq0 hqmin
  have hselected : Set.EqOn q.curve (A.path Z b hb hmax).curve (Set.Icc 0 b) := by
    rw [A.path_eq]
    exact heq
  exact ⟨Z, (heq (show b ∈ Set.Icc 0 b from ⟨hb.le, le_rfl⟩)).symm.trans hqb,
    (isMinimizingBackwardLPath_iff_of_eqOn q (A.path Z b hb hmax) hselected).mp hqmin⟩

theorem lExponentialFamily_reducedLength_le_action (hL : LGeodesicTheory F T τmax)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    reducedLength F T p (A.gamma Z b) b ≤ A.action Z b / (2 * Real.sqrt b) := by
  have h0 : (A.path Z b hb hmax).curve 0 = p :=
    (congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)
  have hend := congrFun (A.path_eq Z b hb hmax) b
  have h := reducedLength_le_path hL hb hmax.le (A.path Z b hb hmax) h0 hend
  simpa only [A.path_eq, LExponentialFamily.action] using h

theorem lExponentialFamily_reducedLength_eq_action_iff (hL : LGeodesicTheory F T τmax)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    reducedLength F T p (A.gamma Z b) b = A.action Z b / (2 * Real.sqrt b) ↔
      IsMinimizingBackwardLPath F T 0 b (A.path Z b hb hmax) := by
  have h0 : (A.path Z b hb hmax).curve 0 = p :=
    (congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)
  have hend := congrFun (A.path_eq Z b hb hmax) b
  have hden : 0 < 2 * Real.sqrt b := mul_pos zero_lt_two (Real.sqrt_pos.mpr hb)
  constructor
  · intro heq q hq0 hqb
    have h := reducedLength_le_path hL hb hmax.le q (hq0.trans h0) (hqb.trans hend)
    rw [heq] at h
    have haction := (div_le_div_iff_of_pos_right hden).mp h
    simpa only [A.path_eq, LExponentialFamily.action] using haction
  · intro hmin
    have h := reducedLength_eq_minimizing_path hL hb hmax.le (A.path Z b hb hmax) h0 hend hmin
    simpa only [A.path_eq, LExponentialFamily.action] using h

end PoincareConjecture.Proofs.M09
