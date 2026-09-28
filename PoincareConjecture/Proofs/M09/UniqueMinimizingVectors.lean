import PoincareConjecture.Proofs.M09.MinimizingInitialVectors



set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem lExponentialFamily_uniqueMinimizing_iff (hM04 : RicciFlowCurvatureTheory.{u})
    (hL : LGeodesicTheory F T τmax) (hτmax : 0 < τmax)
    (hwindow : Set.Icc (T - τmax) T ⊆ J) (A : LExponentialFamily F T τmax p)
    (Z : TangentSpace (𝓡 n) p) (τ : ℝ) (ht : 0 < τ) (hm : τ < τmax) :
    A.uniqueMinimizing Z τ ↔
      IsMinimizingBackwardLPath F T 0 τ (A.path Z τ ht hm) ∧
      ∀ W, A.gamma W τ = A.gamma Z τ →
        IsMinimizingBackwardLPath F T 0 τ (A.path W τ ht hm) → W = Z := by
  constructor
  · rintro ⟨ht', hm', hmin, huniq⟩
    refine ⟨hmin, ?_⟩
    intro W hend hWmin
    have heq := huniq (A.path W τ ht hm)
      ((congrFun (A.path_eq W τ ht hm) 0).trans (A.gamma_at_zero W))
      ((congrFun (A.path_eq W τ ht hm) τ).trans hend) hWmin
    rw [A.path_eq] at heq
    exact lExponentialFamily_initialVector_eq_of_eqOn A W Z τ ht hm heq
  · rintro ⟨hmin, hvec⟩
    refine ⟨ht, hm, hmin, ?_⟩
    intro q hq0 hqτ hqmin
    obtain ⟨W, heq, _⟩ := lExponentialFamily_minimizers_lift hM04 hL hτmax hwindow
      A τ ht hm q hq0 hqmin
    have hselected : Set.EqOn q.curve (A.path W τ ht hm).curve (Set.Icc 0 τ) := by
      rw [A.path_eq]
      exact heq
    have hWmin := (isMinimizingBackwardLPath_iff_of_eqOn q (A.path W τ ht hm) hselected).mp hqmin
    have hend : A.gamma W τ = A.gamma Z τ :=
      (heq (show τ ∈ Set.Icc 0 τ from ⟨ht.le, le_rfl⟩)).symm.trans hqτ
    simpa only [hvec W hend hWmin] using heq

end PoincareConjecture.Proofs.M09
