import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.TwoDimensional.Compact.Rigidity.Roundness

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

namespace PoincareConjecture

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]
  [ConnectedSpace M]

theorem LeviCivitaData.constantPositiveSectionalCurvature_of_surface_shrinker
    {g : RiemannianMetric 2 M} (D : LeviCivitaData g) (hc : MetricComplete g)
    {f : M → ℝ} {lambda : ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) 2 f)
    (hlambda : 0 < lambda)
    (hsol : ∀ x, ∀ v w : TangentSpace (𝓡 2) x,
      D.ricci x v w + D.hessian f x v w = lambda * g.inner x v w)
    (hoperator : ∀ x, D.NonnegativeCurvatureOperator x)
    (hnonflat : ∃ x, D.curvatureTensorNorm x ≠ 0) :
    ConstantPositiveSectionalCurvature g D := by
  let : CompactSpace M :=
    D.compactSpace_of_surface_shrinker hc hf hlambda hsol hoperator hnonflat
  exact D.constantPositiveSectionalCurvature_of_compact_surface_soliton hlambda hf hsol
    (fun x => D.scalar_nonnegative_of_nonnegative_curvatureOperator x (hoperator x))

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [SecondCountableTopology M]

theorem GradientShrinkingSolitonData.round (S : GradientShrinkingSolitonData 2 M) :
    ConstantPositiveSectionalCurvature S.metric S.connection :=
  S.connection.constantPositiveSectionalCurvature_of_surface_shrinker S.complete
    S.potential_C2 (by norm_num : (0 : ℝ) < 1 / 2) S.soliton_equation
    S.nonnegative_curvature S.nonflat

end PoincareConjecture
