import PoincareConjecture.Proofs.M09.VariationRegularField
import PoincareConjecture.Proofs.M09.InitialVariationJet








set_option autoImplicit false
set_option maxSynthPendingDepth 3

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M09

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in
theorem initialVectorVariation_hasLJacobiInitialDerivative
    (hτmax : 0 < τmax) (hwindow : Set.Icc (T - τmax) T ⊆ J)
    (A : LExponentialFamily F T τmax p) (Z W : TangentSpace (𝓡 n) p)
    (b : ℝ) (hb : 0 < b) (hmax : b < τmax) :
    HasLJacobiInitialDerivative (A.regularization Z b hb hmax)
      (variationField (initialVectorVariation A Z W b hb hmax).toLVariation)
      (((congrFun (A.path_eq Z b hb hmax) 0).trans (A.gamma_at_zero Z)).symm ▸
        ((2 : ℝ) • W)) := by
  let V := (initialVectorVariation A Z W b hb hmax).toLVariation
  obtain ⟨E⟩ := nonempty_variationFieldExtension V
  obtain ⟨D, hD⟩ := exists_sqrtRegularField_of_variation_extension τmax hτmax hmax hwindow
    (A.regularization Z b hb hmax).path V E
  have hzero : (0 : ℝ) ∈ sqrtParameterInterval 0 b := by
    simp only [sqrtParameterInterval, Real.sqrt_zero, Set.mem_Icc, le_refl, true_and]
    exact Real.sqrt_nonneg b
  have hv : (D.firstDerivative 0 : EuclideanSpace ℝ (Fin n)) = (2 : ℝ) • W :=
    (hD 0 hzero).trans (initialVectorVariation_initial_pullback A Z W b hb hmax E)
  refine ⟨D, ?_⟩
  have hcast (x y : M) (h : x = y) (v : TangentSpace (𝓡 n) x) :
      (h ▸ v : TangentSpace (𝓡 n) y) = (show TangentSpace (𝓡 n) y from v) := by
    cases h
    rfl
  dsimp only
  simp only [hcast]
  exact (congrArg (fun s : ℝ ↦ (D.firstDerivative s : EuclideanSpace ℝ (Fin n)))
    Real.sqrt_zero).trans hv

end PoincareConjecture.Proofs.M09
