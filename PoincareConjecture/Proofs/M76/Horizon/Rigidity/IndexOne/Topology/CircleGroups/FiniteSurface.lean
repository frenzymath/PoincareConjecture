import PoincareConjecture.Proofs.M76.Horizon.Rigidity.IndexOne.Topology.CircleGroups.CocycleRank
import PoincareConjecture.Proofs.M76.Mathlib.FiniteBarycentricCoordinates
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FiniteCarrierLocalPathConnected
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RetractionFundamentalGroup
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComponentParity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere

set_option autoImplicit false

open Set PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem incidence_rank_le_one_of_isCyclic
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hconn : IsConnected K.space)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    letI : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
    let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + 1 := by
  classical
  let : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
  let : ConnectedSpace K.space := isConnected_iff_connectedSpace.mp hconn
  let : LocallyPathConnectedSpace K.space := K.locallyPathConnectedSpace_of_finite hK
  let : PathConnectedSpace K.space := .of_locallyPathConnectedSpace
  let H := K.finiteBarycentricHomeomorph
  let q := H.symm x
  let : PathConnectedSpace K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace :=
    H.symm.surjective.pathConnectedSpace H.symm.continuous
  let : IsCyclic (FundamentalGroup K.space (H q)) := by
    have hq : H q = x := H.apply_symm_apply x
    rw [hq]
    infer_instance
  let : IsCyclic (FundamentalGroup
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex.barycentricSpace q) :=
    isCyclic_of_injective (FundamentalGroup.map ⟨H, H.continuous⟩ q)
      (FundamentalGroup.map_injective_of_leftInverse ⟨H, H.continuous⟩ ⟨H.symm, H.symm.continuous⟩
        H.left_inv q)
  exact finrank_closed_le_finrank_coboundaries_add_one_of_isCyclic _
    K.vertexAbstractComplex.singleton_mem q

open Classical in

theorem surfaceEulerCount_eq_two_of_isCyclic_and_geometric_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    K.surfaceEulerCount = 2 := by
  classical
  by_contra hne
  have hlo := (K.closed_surface_rank_ge_two_of_geometric_signs hK hpure hconn hlinks
    hcofaces number hnumber sign hcancel hne).2
  have hhi := K.incidence_rank_le_one_of_isCyclic hK hconn x
  dsimp only at hlo hhi
  omega

open Classical in

theorem exists_sphere_model_of_isCyclic_and_geometric_signs
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 → t ≠ u →
      ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [IsCyclic (FundamentalGroup K.space x)] :
    ∃ H : K.space ≃ₜ frontier (TriangularRoofModel.halfBall 1), H.IsFinitePL := by
  classical
  exact K.exists_sphere_model_of_surfaceEulerCount_eq_two hK hpure hcofaces hlinks hconn
    (K.surfaceEulerCount_eq_two_of_isCyclic_and_geometric_signs hK hpure hconn hlinks
      hcofaces number hnumber sign hcancel x)

end Geometry.SimplicialComplex
