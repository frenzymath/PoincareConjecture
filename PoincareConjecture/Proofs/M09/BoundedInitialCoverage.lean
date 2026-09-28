import PoincareConjecture.Proofs.M09.SmallTimeExponential
import PoincareConjecture.Proofs.M09.SmallTimeActionBound
import PoincareConjecture.Proofs.M09.UniqueMinimizingVectors

set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M] [ConnectedSpace M] [T3Space M] [SecondCountableTopology M]

theorem lExponentialFamily_bounded_initial_coverage {J : Set ℝ}
    (F : RicciFlow n M J) (hM04 : RicciFlowCurvatureTheory.{u})
    (T τmax : ℝ) (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Set.Icc (T - τmax) T))
    (hL : LGeodesicTheory F T τmax) (p : M) (A : LExponentialFamily F T τmax p)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ δ : ℝ, 0 < δ ∧ δ < τmax ∧ ∀ Z : TangentSpace (𝓡 n) p,
      (F.metric T).tangentNorm p Z ≤ a → ∀ τ, 0 < τ → τ < δ →
        (Z, τ) ∈ A.regularDomain := by
  let b := τmax / 2
  have hb : 0 < b := by dsimp [b]; linarith
  have hbmax : b < τmax := by dsimp [b]; linarith
  obtain ⟨R, hR, haR, hcompetitor⟩ := lExponentialFamily_minimizing_competitors_bounded
    F hM04 T τmax hτmax hwindow hcurvature p A b hb hbmax a ha
  obtain ⟨d, hd, _, hsmall⟩ := lExponentialFamily_smallTime_injective hτmax A R hR
  refine ⟨min b d, lt_min hb hd, (min_le_left _ _).trans_lt hbmax, ?_⟩
  intro Z hZ τ hτ hτδ
  have hτb : τ ≤ b := (hτδ.trans_le (min_le_left _ _)).le
  have hτmax' := hτb.trans_lt hbmax
  obtain ⟨hinj, hbij⟩ := hsmall τ hτ (hτδ.trans_le (min_le_right _ _))
  have hZR : (F.metric T).tangentNorm p Z ≤ R := hZ.trans haR
  have huniq (W : TangentSpace (𝓡 n) p) (hend : A.gamma W τ = A.gamma Z τ)
      (hmin : IsMinimizingBackwardLPath F T 0 τ (A.path W τ hτ hτmax')) : W = Z :=
    hinj (hcompetitor Z hZ τ hτ hτb W hend hmin) hZR hend
  obtain ⟨W, hend, hmin⟩ := lExponentialFamily_exists_minimizing_initialVector
    hM04 hL hτmax hwindow A τ hτ hτmax' (A.gamma Z τ)
  have hWZ := huniq W hend hmin
  have hZmin : IsMinimizingBackwardLPath F T 0 τ (A.path Z τ hτ hτmax') := by
    simpa only [hWZ] using hmin
  exact ⟨(lExponentialFamily_uniqueMinimizing_iff hM04 hL hτmax hwindow A Z τ hτ hτmax').mpr
    ⟨hZmin, huniq⟩, hbij Z hZR⟩

end PoincareConjecture.Proofs.M09
