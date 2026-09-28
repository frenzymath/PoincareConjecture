import PoincareConjecture.Statements.M12MovingGaugeTheory










set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u v

namespace PoincareConjecture.M34

noncomputable section

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I K : SpacetimeInterval} {S : GeneralizedFlowSpacetime n X time I}
  {D : SmoothSpacetimeInterval K} {M : Type v} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

set_option backward.isDefEq.respectTransparency false in


theorem compatibleCylinder_mfderiv_prod (e : CompatibleSpacetimeCylinder S D M)
    (g : SpacetimeCylinderMetric e) (t : D.Point) (x : M) (a : ℝ)
    (v : TangentSpace (𝓡 n) x) :
    mfderiv (spacetimeModel n) (spacetimeModel n) e.toSpacetime (t, x)
      (a • D.positiveTangent t, v) =
      a • S.timeVector (e.toSpacetime (t, x)) + (g.spatialTangentEquiv t x v).val := by
  let : NormedAddCommGroup (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin 1)))
  let : NormedSpace ℝ (TangentSpace (𝓡∂ 1) t) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin 1)))
  let : NormedAddCommGroup (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
  let : NormedSpace ℝ (TangentSpace (𝓡 n) x) :=
    inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
  let : NormedAddCommGroup (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedAddCommGroup (SpacetimeModelVector n))
  let : NormedSpace ℝ (TangentSpace (spacetimeModel n) (e.toSpacetime (t, x))) :=
    inferInstanceAs (NormedSpace ℝ (SpacetimeModelVector n))
  have hprod := mfderiv_prod_eq_add_apply (p := (t, x))
    (e.smooth.mdifferentiableAt (by simp)) (v := (a • D.positiveTangent t, v))
  dsimp only at hprod
  rw [map_smul, e.worldline_derivative, ← g.spatialTangentEquiv_eq] at hprod
  exact hprod

end

end PoincareConjecture.M34
