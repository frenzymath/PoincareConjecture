import PoincareConjecture.Proofs.Horizon.Geometry.Manifold.Covering.LocalDiffeomorph
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Splitting.UnitCover
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalDiffeomorph

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.RicciFlow.Splitting

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} (D : LeviCivitaData g)
  (hc : IsCoveringMap (unitRicciKernelProjection D))

@[reducible] def unitRicciKernelChartedSpace :
    ChartedSpace (EuclideanSpace ℝ (Fin n)) (UnitRicciKernel D) :=
  Poincare.Manifold.LocalHomeomorphLift.chartedSpace hc.isLocalHomeomorph

theorem unitRicciKernelIsManifold :
    letI := unitRicciKernelChartedSpace D hc
    IsManifold (𝓡 n) ∞ (UnitRicciKernel D) :=
  Poincare.Manifold.LocalHomeomorphLift.isManifold hc.isLocalHomeomorph (𝓡 n) ∞

theorem unitRicciKernelProjection_isLocalDiffeomorph :
    letI := unitRicciKernelChartedSpace D hc
    IsLocalDiffeomorph (𝓡 n) (𝓡 n) ∞ (unitRicciKernelProjection D) :=
  Poincare.Manifold.LocalHomeomorphLift.isLocalDiffeomorph hc.isLocalHomeomorph (𝓡 n) ∞

def unitRicciKernelMetric :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    RiemannianMetric n (UnitRicciKernel D) := by
  letI := unitRicciKernelChartedSpace D hc
  letI := unitRicciKernelIsManifold D hc
  exact g.pullbackOfLocalDiffeomorph (unitRicciKernelProjection D)
    (unitRicciKernelProjection_isLocalDiffeomorph D hc)

theorem unitRicciKernelReverse_contMDiff :
    letI := unitRicciKernelChartedSpace D hc
    ContMDiff (𝓡 n) (𝓡 n) ∞ (unitRicciKernelReverse D) := by
  let := unitRicciKernelChartedSpace D hc
  apply Poincare.Manifold.LocalHomeomorphLift.contMDiff_of_continuous_projection
    hc.isLocalHomeomorph (𝓡 n) ∞ (continuous_unitRicciKernelReverse D)
  exact (unitRicciKernelProjection_isLocalDiffeomorph D hc).contMDiff

def unitRicciKernelDeckDiffeomorph :
    letI := unitRicciKernelChartedSpace D hc
    Diffeomorph (𝓡 n) (𝓡 n) (UnitRicciKernel D) (UnitRicciKernel D) ∞ := by
  letI := unitRicciKernelChartedSpace D hc
  exact { (unitRicciKernelDeckHomeomorph D).toEquiv with
    contMDiff_toFun := unitRicciKernelReverse_contMDiff D hc
    contMDiff_invFun := unitRicciKernelReverse_contMDiff D hc }

theorem unitRicciKernelReverse_preserves_metric :
    letI := unitRicciKernelChartedSpace D hc
    letI := unitRicciKernelIsManifold D hc
    ∀ (p : UnitRicciKernel D) (v w : TangentSpace (𝓡 n) p),
      (unitRicciKernelMetric D hc).inner (unitRicciKernelReverse D p)
        (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse D) p v)
        (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse D) p w) =
      (unitRicciKernelMetric D hc).inner p v w := by
  let := unitRicciKernelChartedSpace D hc
  let := unitRicciKernelIsManifold D hc
  intro p v w
  have hp := (unitRicciKernelProjection_isLocalDiffeomorph D hc).mdifferentiable
    (by simp)
  have hr := (unitRicciKernelReverse_contMDiff D hc).mdifferentiable (by simp)
  have hd :
      (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) (unitRicciKernelReverse D p)).comp
        (mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse D) p) =
      mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) p :=
    (mfderiv_comp p (hp _) (hr p)).symm
  change g.inner (unitRicciKernelProjection D p)
      ((mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) (unitRicciKernelReverse D p))
        ((mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse D) p) v))
      ((mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelProjection D) (unitRicciKernelReverse D p))
        ((mfderiv (𝓡 n) (𝓡 n) (unitRicciKernelReverse D) p) w)) = _
  rw [← ContinuousLinearMap.comp_apply, hd, ← ContinuousLinearMap.comp_apply, hd]
  rfl

end PoincareConjecture.RicciFlow.Splitting
