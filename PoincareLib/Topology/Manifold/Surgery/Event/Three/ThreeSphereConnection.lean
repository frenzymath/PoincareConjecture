import PoincareLib.Topology.Manifold.Surgery.Event.Three.ThreeSphereMetric
import PoincareLib.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareLib.Geometry.Riemannian.Connection.EuclideanConstruction
import PoincareLib.Geometry.Riemannian.Connection.Descent

/-!
# The standard sphere connection from its actual charts

Inverse stereographic charts cover the three-sphere by local diffeomorphisms
from Euclidean three-space. Pulling back the actual induced sphere metric,
constructing its Euclidean Levi-Civita connections, and descending those
connections yields a smooth torsion-free metric connection on the sphere.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareMT.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

/-- Inverse stereographic projection as a total map into the actual sphere. -/
noncomputable def threeSphereStereoInverse (a : UnitThreeSphere) :
    EuclideanSpace ℝ (Fin 3) → UnitThreeSphere := (stereographic' 3 a).symm

/-- Both directions of the stored stereographic atlas chart are smooth.
Its inverse has all of Euclidean three-space as its source. -/
theorem threeSphereStereoLocalDiffeomorph (a : UnitThreeSphere) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (threeSphereStereoInverse a) := by
  let e := stereographic' 3 a
  have hatlas : e ∈ atlas (EuclideanSpace ℝ (Fin 3)) UnitThreeSphere := ⟨a, rfl⟩
  have hmax : e ∈ IsManifold.maximalAtlas (𝓡 3) ∞ UnitThreeSphere :=
    IsManifold.subset_maximalAtlas hatlas
  let d : PartialDiffeomorph (𝓡 3) (𝓡 3)
      (EuclideanSpace ℝ (Fin 3)) UnitThreeSphere ∞ :=
    { toPartialEquiv := e.symm.toPartialEquiv
      open_source := e.symm.open_source
      open_target := e.symm.open_target
      contMDiffOn_toFun := by
        convert! contMDiffOn_symm_of_mem_maximalAtlas hmax using 1
      contMDiffOn_invFun := by
        convert! contMDiffOn_of_mem_maximalAtlas hmax using 1 }
  intro z
  refine ⟨d, ?_, fun _ _ => rfl⟩
  change z ∈ e.target
  simp only [e, stereographic'_target, Set.mem_univ]

/-- Choosing the opposite pole puts each point in one inverse-chart image. -/
theorem threeSphereStereo_cover (x : UnitThreeSphere) :
    ∃ a z, threeSphereStereoInverse a z = x := by
  refine ⟨-x, stereographic' 3 (-x) x, ?_⟩
  apply (stereographic' 3 (-x)).left_inv
  simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ x

/-- Construct an actual smooth metric-compatible torsion-free connection on
the induced round sphere metric. Curvature is not asserted by this definition. -/
noncomputable def threeSphereConnection : LeviCivitaData threeSphereMetric := by
  let h (a : UnitThreeSphere) : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3)) :=
    threeSphereMetric.pullbackOfLocalDiffeomorph (threeSphereStereoInverse a)
      (threeSphereStereoLocalDiffeomorph a)
  refine threeSphereMetric.leviCivitaDataOfCover h
    (fun a => (h a).euclideanLeviCivitaData) threeSphereStereoInverse
    (fun a => (threeSphereStereoLocalDiffeomorph a).contMDiff) ?_
    (fun _ _ _ _ => rfl) threeSphereStereo_cover
  intro a z
  change ((threeSphereStereoLocalDiffeomorph a).mfderivToContinuousLinearEquiv
    (by simp) z).toContinuousLinearMap.IsInvertible
  exact ContinuousLinearMap.isInvertible_equiv

end PoincareMT.M38
