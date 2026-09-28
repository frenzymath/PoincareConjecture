import PoincareConjecture.Proofs.M76.Mathlib.ClosedStarInteriorBall
import PoincareConjecture.Proofs.M76.Mathlib.ConvexBoundaryExtension
import PoincareConjecture.Proofs.M02.SphereConnectivity
import PoincareConjecture.Proofs.M02.Topology.SphereDiskExtension










set_option autoImplicit false

open Set Metric

namespace Geometry

local notation "V3" => (Fin 3 → ℝ)




theorem unitThreeSphere_lifting_properties :
    SimplyConnectedSpace (sphere (0 : V3) 1) ∧
      LocallyPathConnectedSpace (sphere (0 : V3) 1) := by
  let c : V3 ≃L[ℝ] EuclideanSpace ℝ (Fin 3) :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  let H := PoincareConjecture.Proofs.M02.Topology.unitSphereHomeomorph c
  let : SimplyConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    PoincareConjecture.Proofs.M02.sphere_simplyConnectedSpace_of_two_lt_finrank (by simp)
  let : LocallyPathConnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    ChartedSpace.locallyPathConnectedSpace (H := EuclideanSpace ℝ (Fin 2))
      (M := sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  exact ⟨H.toHomotopyEquiv.simplyConnectedSpace,
    H.isOpenEmbedding.locallyPathConnectedSpace⟩

namespace SimplicialComplex




theorem exists_faceLink_singleton_sphere_homeomorph_of_interior
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {p : V3} (hp : p ∈ K.vertices) (hint : p ∈ interior K.space) :
    Nonempty ((K.faceLink {p}).space ≃ₜ sphere (0 : V3) 1) := by
  classical
  obtain ⟨hrim, C, hC, hcv, hne, e, _, heb⟩ :=
    K.isFinitePLBallPair_closedStar_of_interior hK hp hint (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_, hb, _⟩ := hC.exists_compatible_unitBall_models hcv hne
  let H := (e.restrictSubsets hrim hC.isClosed.frontier_subset heb).trans hb
  rw [faceLink_singleton_eq_link]
  exact ⟨H⟩



theorem faceLink_singleton_lifting_properties_of_interior
    (K : SimplicialComplex ℝ V3) (hK : K.faces.Finite)
    {p : V3} (hp : p ∈ K.vertices) (hint : p ∈ interior K.space) :
    SimplyConnectedSpace (K.faceLink {p}).space ∧
      LocallyPathConnectedSpace (K.faceLink {p}).space := by
  obtain ⟨H⟩ := K.exists_faceLink_singleton_sphere_homeomorph_of_interior hK hp hint
  let : SimplyConnectedSpace (sphere (0 : V3) 1) := unitThreeSphere_lifting_properties.1
  let : LocallyPathConnectedSpace (sphere (0 : V3) 1) := unitThreeSphere_lifting_properties.2
  exact ⟨H.toHomotopyEquiv.simplyConnectedSpace,
    H.isOpenEmbedding.locallyPathConnectedSpace⟩

end SimplicialComplex

end Geometry
