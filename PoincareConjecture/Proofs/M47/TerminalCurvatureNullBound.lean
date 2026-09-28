import PoincareConjecture.Proofs.M47.TerminalCurvatureCalibratedBound
import PoincareConjecture.Proofs.M47.TerminalCurvatureStaticGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set VectorField
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47

open RicciFlow.Splitting

theorem terminalCurvature_null_bound_of_neck_readout
    {epsilon A H : ℝ} (hsmall : epsilon ≤ 1 / 200)
    {M : Type u} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hC : RicciFlowCurvatureTheory.{u}) (hcomplete : MetricComplete g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x) (cover : NullOrientationCover D)
    (hrank : ∀ x, ricciNullity D x = 1)
    (hsections : ∀ p : UnitRicciKernel D,
      ∃ (U : Set M) (V : (y : M) → TangentSpace (𝓡 3) y),
        IsOpen U ∧ p.val.proj ∈ U ∧
        ContMDiffOn (𝓡 3) ((𝓡 3).prod (𝓡 3)) ∞ (T% V) U ∧ V p.val.proj = p.val.snd ∧
        ∀ y ∈ U, g.inner y (V y) (V y) = 1 ∧
          (∀ w, D.ricci y (V y) w = 0) ∧ ∀ w, D.connection V y w = 0)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨ IsCompact (univ : Set M)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  classical
  by_cases hhigh : ∃ x, H ≤ D.scalarCurvature x
  · obtain ⟨x, hx⟩ := hhigh
    rcases hreadout x hx with ⟨N, _, he, _⟩ | hc
    · have hsec : D.NonnegativeSectionalCurvature := fun y =>
        D.curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator y (hoperator y)
      exact terminalCurvature_calibrated_null_cover_bound D hC hcomplete hsec cover
        hrank hsections N (he ▸ hsmall)
    · exact terminalCurvature_compact_bound D hc
  · refine ⟨max 1 H, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
    intro x
    have hx : D.scalarCurvature x < H := lt_of_not_ge (fun hx => hhigh ⟨x, hx⟩)
    exact (D.curvatureTensorNorm_le_scalarCurvature_sharp (hC.tensor_calculus 3 M g D)
      x (hoperator x)).trans (hx.le.trans (le_max_right _ _))

end PoincareConjecture.M47
