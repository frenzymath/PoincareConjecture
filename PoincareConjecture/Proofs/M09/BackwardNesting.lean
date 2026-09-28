import PoincareConjecture.Proofs.M09.StrictPrefixUniqueness
import PoincareConjecture.Proofs.M09.StrictPrefixNonconjugacy





set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [ConnectedSpace M] [T2Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

theorem lExponentialFamily_regularDomain_strict_prefix
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (c b : ℝ) (hc : 0 < c) (hcb : c < b) (hmax : b < τmax)
    (hmin : IsMinimizingBackwardLPath F T 0 b (A.path Z b (hc.trans hcb) hmax)) :
    (Z, c) ∈ A.regularDomain :=
  ⟨lExponentialFamily_uniqueMinimizing_prefix hM04 hL hτmax hwindow A Z c b hc hcb hmax hmin,
    lExponentialFamily_sliceDifferential_prefix_bijective hM04 hL hτmax hwindow
      A Z c b hc hcb hmax hmin⟩

theorem lExponentialFamily_backward_nesting
    (hM04 : RicciFlowCurvatureTheory.{u}) (hL : LGeodesicTheory F T τmax)
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : (Z, b) ∈ A.regularDomain) (c : ℝ) (hc : 0 < c) (hcb : c ≤ b) :
    (Z, c) ∈ A.regularDomain := by
  rcases lt_or_eq_of_le hcb with hlt | rfl
  · obtain ⟨_, hmax, hmin, _⟩ := hb.1
    exact lExponentialFamily_regularDomain_strict_prefix hM04 hL hτmax hwindow A Z c b
      hc hlt hmax hmin
  · exact hb

end PoincareConjecture.Proofs.M09
