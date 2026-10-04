import PoincareLib.Topology.Homotopy.LoopSpace.Contraction.Extension
import PoincareLib.Geometry.Riemannian.LoopSpace.Area.Basic
import Mathlib.Topology.Instances.Matrix

/-!
# Integrability of the metric area of C1 disks

Morgan--Tian Definition 18.17, printed p. 430, and Corollary 18.28, p. 434,
use actual parametrized area. A global C1 disk map has continuous metric
Jacobian density, hence an integrable density on the compact unit disk.
This excludes reliance on the totalized value of a nonintegrable integral.
See the task's disk-extension derivation.
-/

set_option autoImplicit false

open Set MeasureTheory Bundle
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.LoopSpace

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace LoopAmbient M] [IsManifold (𝓡 3) ∞ M]

/-- The contract's metric Jacobian is pointwise nonnegative. Source:
MT Definition 18.17, printed p. 430. -/
theorem parametrizedAreaDensity_nonneg (g : RiemannianMetric 3 M)
    (F : LoopPlane → M) (z : LoopPlane) : 0 ≤ parametrizedAreaDensity g F z :=
  Real.sqrt_nonneg _

/-- Each derivative column of a C1 disk map is continuous in the tangent
bundle. Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem continuous_disk_derivative_column {F : LoopPlane → M}
    (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) (i : Fin 2) :
    Continuous (fun z : LoopPlane =>
      (⟨F z, mfderiv (𝓡 2) (𝓡 3) F z (EuclideanSpace.basisFun (Fin 2) ℝ i)⟩ :
        TangentBundle (𝓡 3) M)) :=
  (hF.continuous_tangentMap le_rfl).comp
    ((tangentBundleModelSpaceHomeomorph (𝓡 2)).symm.continuous.comp
      (continuous_id.prodMk continuous_const))

/-- A C1 map has a continuous metric Jacobian density. Source:
MT Corollary 18.28, p. 434, disk-extension derivation. -/
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

/-- The area density of a C1 map is genuinely integrable on the unit disk.
Source: MT Corollary 18.28, p. 434, disk-extension derivation. -/
theorem integrableOn_parametrizedAreaDensity (g : RiemannianMetric 3 M)
    {F : LoopPlane → M} (hF : ContMDiff (𝓡 2) (𝓡 3) 1 F) :
    IntegrableOn (parametrizedAreaDensity g F) loopDiskSet volume :=
  (continuous_parametrizedAreaDensity g hF).continuousOn.integrableOn_compact
    (isCompact_closedBall 0 1)

/-- Parametrized area is nonnegative, including degenerate disks. Source:
MT Definition 18.17, p. 430, and Corollary 18.28, p. 434. -/
theorem parametrizedRiemannianArea_nonneg (g : RiemannianMetric 3 M)
    (F : LoopPlane → M) : 0 ≤ parametrizedRiemannianArea g F :=
  integral_nonneg (parametrizedAreaDensity_nonneg g F)

end PoincareMT.LoopSpace
