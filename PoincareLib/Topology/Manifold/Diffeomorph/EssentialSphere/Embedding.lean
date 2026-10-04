import PoincareLib.Topology.Manifold.Diffeomorph.EssentialSphere.RadialCylinder
import PoincareLib.Geometry.Manifold.SmoothEmbedding.Slice
import PoincareLib.Geometry.Manifold.SmoothEmbedding.LocalDiffeomorph
import PoincareLib.Geometry.Manifold.OpenEmbedding

/-!
# The central sphere of a smooth collar

The original collar supplies the smooth embedding required by ambient
Schoenflies, including after transport to punctured Euclidean coordinates.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

namespace Poincare

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "S2" => Metric.sphere (0 : E3) 1
local notation "CylModel" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)

/-- The center of a smooth full sphere collar is a smooth embedding. -/
theorem isSmoothEmbedding_collar_center
    {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace E3 Y] [IsManifold (𝓡 3) ∞ Y]
    (c : OpenPartialHomeomorph (S2 × ℝ) Y)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    (hsource : ∀ q : S2, (q, (0 : ℝ)) ∈ c.source) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ (fun q : S2 => c (q, 0)) :=
  c.isSmoothEmbedding_slice hc hci
    (ContinuousLinearEquiv.ofFinrankEq (by simp)) 0 hsource

/-- The central collar sphere satisfies the smooth-embedding hypothesis of
Euclidean Schoenflies in the given punctured-space coordinates. -/
theorem isSmoothEmbedding_collar_center_in_punctured_model
    {Y : Type*} [TopologicalSpace Y]
    [ChartedSpace E3 Y] [IsManifold (𝓡 3) ∞ Y]
    (J : Diffeomorph (𝓡 3) (𝓡 3) Y puncturedThreeSpace ∞)
    (c : OpenPartialHomeomorph (S2 × ℝ) Y)
    (hc : ContMDiffOn CylModel (𝓡 3) ∞ c c.source)
    (hci : ContMDiffOn (𝓡 3) CylModel ∞ c.symm c.target)
    (hsource : ∀ q : S2, (q, (0 : ℝ)) ∈ c.source) :
    _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞
      (fun q : S2 => (J (c (q, 0)) : E3)) := by
  have hf := isSmoothEmbedding_collar_center c hc hci hsource
  have hJ : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun y => (J y : E3)) := by
    intro y
    exact (J.isLocalDiffeomorph y).comp (𝓡 3) E3
      (isLocalDiffeomorph_opensSubtypeVal (𝓡 3) puncturedThreeSpace (J y))
  exact hf.comp_localDiffeomorph hJ
    (fun _ _ h => hf.isEmbedding.injective (J.injective (Subtype.ext h)))

end Poincare
