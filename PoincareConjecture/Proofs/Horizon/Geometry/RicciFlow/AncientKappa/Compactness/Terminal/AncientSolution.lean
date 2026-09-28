import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Nonflatness










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.RicciFlow

variable {M : Type} [TopologicalSpace M] [MeasurableSpace M] [BorelSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]



def ancientKappaSolutionOfTerminalScalarBound
    (F : RicciFlow 3 M (Iic 0)) (P : M23NormalizedKappaCompactnessPredecessors)
    {κ B : ℝ} (hκ : 0 < κ) (hB : 0 ≤ B)
    (hcomplete : ∀ t : ℝ, t ≤ 0 → MetricComplete (F.metric t))
    (hoperator : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      (F.connection t).NonnegativeCurvatureOperator x)
    (hnc : AncientKappaNoncollapsed F κ)
    (hpositive : ∃ p : M, 0 < (F.connection 0).scalarCurvature p)
    (hpast : ∀ t : ℝ, t ≤ 0 → ∀ x : M,
      |(F.connection t).curvatureTensorNorm x| ≤ (F.connection 0).scalarCurvature x)
    (hbound : ∀ x : M, (F.connection 0).scalarCurvature x ≤ B) :
    AncientKappaSolution 3 M := by
  have hcurv (t : ℝ) (ht : t ≤ 0) (x : M) :
      (F.connection t).curvatureTensorNorm x ≤ B :=
    (le_abs_self _).trans ((hpast t ht x).trans (hbound x))
  have hnonflat := F.scalarCurvature_positive_somewhere_of_bounded_ancient_of_m23_predecessors
    P hcomplete hoperator hB hcurv hpositive
  exact {
    flow := F
    kappa := κ
    kappa_pos := hκ
    complete := hcomplete
    nonnegative_curvature_operator := hoperator
    bounded_curvature := fun t ht => ⟨B, hB, fun x => (hpast t ht x).trans (hbound x)⟩
    nonflat := fun t ht => by
      obtain ⟨x, hx⟩ := hnonflat t ht
      refine ⟨x, fun hz => ?_⟩
      have h := (F.connection t).abs_scalarCurvature_le_curvatureTensorNorm x
      rw [hz, mul_zero] at h
      exact hx.not_ge ((le_abs_self _).trans h)
    noncollapsed := hnc }

end PoincareConjecture.RicciFlow
