import PoincareConjecture.Proofs.M38.ThreeSphereMetric
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Metric.LocalDiffeomorph
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.EuclideanConstruction
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Connection.Descent










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff Bundle Topology

namespace PoincareConjecture.M38

private instance sphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩


noncomputable def threeSphereStereoInverse (a : UnitThreeSphere) :
    EuclideanSpace ℝ (Fin 3) → UnitThreeSphere := (stereographic' 3 a).symm



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


theorem threeSphereStereo_cover (x : UnitThreeSphere) :
    ∃ a z, threeSphereStereoInverse a z = x := by
  refine ⟨-x, stereographic' 3 (-x) x, ?_⟩
  apply (stereographic' 3 (-x)).left_inv
  simpa only [stereographic'_source, Set.mem_compl_iff, Set.mem_singleton_iff] using
    ne_neg_of_mem_unit_sphere ℝ x



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

end PoincareConjecture.M38
