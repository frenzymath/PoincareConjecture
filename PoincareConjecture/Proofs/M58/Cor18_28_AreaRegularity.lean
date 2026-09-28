import PoincareConjecture.Proofs.M58.Sec18_4_LoopExtension
import Mathlib.Topology.Instances.Matrix











set_option autoImplicit false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.Proofs.M58

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]



theorem parametrizedAreaDensity_nonneg (g : RiemannianMetric 3 M)
    (F : LoopPlane → M) (z : LoopPlane) : 0 ≤ parametrizedAreaDensity g F z :=
  Real.sqrt_nonneg _



theorem continuous_disk_derivative_column {F : LoopPlane → M}
    (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) (i : Fin 2) :
    Continuous (fun z : LoopPlane =>
      (⟨F z, mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
        TangentBundle (𝓡 3) M)) :=
  (hF.continuous_tangentMap le_rfl).comp
    ((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const))



theorem continuous_parametrizedAreaDensity (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    Continuous (parametrizedAreaDensity g F) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle LoopAmbient (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hgram : Continuous (fun z : LoopPlane => fun i j : Fin 2 =>
      g.inner (F z)
        (mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ i))
        (mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ j))) :=
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_disk_derivative_column hF i).inner_bundle (continuous_disk_derivative_column hF j)
  exact (continuous_const.max hgram.matrix_det).sqrt



theorem integrableOn_parametrizedAreaDensity (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    IntegrableOn (parametrizedAreaDensity g F) loopDiskSet volume :=
  (continuous_parametrizedAreaDensity g hF).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 1)



theorem parametrizedRiemannianArea_nonneg (g : RiemannianMetric 3 M)
    (F : LoopPlane → M) : 0 ≤ parametrizedRiemannianArea g F :=
  integral_nonneg (parametrizedAreaDensity_nonneg g F)

end PoincareConjecture.Proofs.M58
