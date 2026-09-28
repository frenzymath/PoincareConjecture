import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Curvature.LocalIsometryInvariants
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Isometry
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Induced.Equivalence







set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Set MeasureTheory
open scoped Manifold ContDiff
namespace PoincareConjecture.LeviCivitaData
variable {n : ℕ} {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [T3Space M] [T3Space N]
  [MeasurableSpace M] [BorelSpace M] [MeasurableSpace N] [BorelSpace N]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) N]
  [IsManifold (𝓡 n) ∞ M] [IsManifold (𝓡 n) ∞ N]
  {g : RiemannianMetric n M} {h : RiemannianMetric n N}


theorem integral_scalarCurvature_eq_of_diffeomorph
    (D : LeviCivitaData g) (D' : LeviCivitaData h)
    (e : M ≃ₘ⟮𝓡 n, 𝓡 n⟯ N)
    (hmetric : ∀ (x : M) (v w : TangentSpace (𝓡 n) x),
      g.inner x v w = h.inner (e x)
        (mfderiv (𝓡 n) (𝓡 n) e x v) (mfderiv (𝓡 n) (𝓡 n) e x w))
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (Ψ : ℝ → E) :
    (∫ x, Ψ (D.scalarCurvature x) ∂g.volumeMeasure) =
      ∫ y, Ψ (D'.scalarCurvature y) ∂h.volumeMeasure := by
  calc
    _ = ∫ x, Ψ (D'.scalarCurvature (e x)) ∂g.volumeMeasure := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x =>
        congrArg Ψ (D.scalarCurvature_eq_of_local_isometry D' isOpen_univ
          e.contMDiff.contMDiffOn (fun x _ => hmetric x) (mem_univ x))
    _ = _ := g.integral_comp_equiv_volumeMeasure h e.toEquiv
      (g.edist_eq_of_diffeomorph_metric_pullback h e hmetric) (fun y => Ψ (D'.scalarCurvature y))
end PoincareConjecture.LeviCivitaData
