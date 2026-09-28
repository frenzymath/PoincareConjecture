import PoincareConjecture.Proofs.M47.TerminalCurvatureStaticGeometry









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M47



theorem terminalCurvature_positive_bound_of_neck_readout
    {epsilon1 epsilon A H : ℝ} (hM45 : M45SmallNeckScaleBound.{u} epsilon1)
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ epsilon1) (hA : 0 < A)
    {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    {g : RiemannianMetric 3 M} (D : LeviCivitaData g)
    (hD : D.CurvatureTensorCalculus) (hcomplete : MetricComplete g)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (hpositive : ∀ x (v w : TangentSpace (𝓡 3) x),
      LeviCivitaData.IsOrthonormalPair g x v w → 0 < D.sectionalCurvature x v w)
    (hreadout : ∀ x, H ≤ D.scalarCurvature x →
      (∃ N : EpsilonNeck g, N.connection = D ∧ N.epsilon = epsilon ∧
        D.scalarCurvature x ≤ A * D.scalarCurvature N.center) ∨ IsCompact (univ : Set M)) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  by_cases hcompact : IsCompact (univ : Set M)
  · exact terminalCurvature_compact_bound D hcompact
  obtain ⟨scale0, hscale0, hscale⟩ := hM45 g D hcomplete hpositive epsilon hepsilon hsmall
  let B := max 1 (max H (A * scale0⁻¹ ^ 2))
  refine ⟨B, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro x
  apply (D.curvatureTensorNorm_le_scalarCurvature_sharp hD x (hoperator x)).trans
  by_cases hx : H ≤ D.scalarCurvature x
  · rcases hreadout x hx with ⟨N, hN, he, hR⟩ | hc
    · have hcenter := terminalCurvature_neck_scalar_le_of_scale N hscale0 (hscale N hN he)
      rw [hN] at hcenter
      exact (hR.trans (mul_le_mul_of_nonneg_left hcenter hA.le)).trans
        ((le_max_right _ _).trans (le_max_right _ _))
    · exact (hcompact hc).elim
  · exact (le_of_not_ge hx).trans ((le_max_left _ _).trans (le_max_right _ _))

end PoincareConjecture.M47
