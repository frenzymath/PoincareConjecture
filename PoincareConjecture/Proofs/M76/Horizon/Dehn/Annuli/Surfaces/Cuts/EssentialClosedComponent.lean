import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Cuts.ClosedComponentParity
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surfaces.Caps.CountTwoSphere
import PoincareConjecture.Proofs.M76.Wall.Mathlib.FinitePLCubeSphereModel
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.InteriorSphereLinks
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Loops.EssentialSquareRim

set_option autoImplicit false
open Set Metric Geometry PreAbstractSimplicialComplex.ModTwoCochains
open AbstractSimplicialComplex TriangularRoofModel

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

open Classical in
theorem simplyConnectedSpace_of_surfaceEulerCount_eq_two
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hcount : K.surfaceEulerCount = 2) : SimplyConnectedSpace K.space := by
  classical
  obtain ⟨H, hH⟩ := K.exists_sphere_model_of_surfaceEulerCount_eq_two
    hK hpure hcofaces hlinks hconn hcount
  have hcv : Convex ℝ (halfBall 1) := by
    rw [halfBall_eq_halfspaces]
    simp only [ofPred_forall]
    exact convex_iInter fun i ↦ (convex_Iic 0).affine_preimage (halfBallForms 1 i)
  obtain ⟨b, _⟩ := hH.exists_unit_cube_sphere_model (isCompact_halfBall (Or.inl rfl)) hcv
    (interior_halfBall_nonempty (h := 1) (Or.inl rfl))
    (by simp [Module.finrank_prod])
  let : SimplyConnectedSpace (sphere (0 : Fin 3 → ℝ) 1) :=
    unitThreeSphere_lifting_properties.1
  exact b.toHomotopyEquiv.simplyConnectedSpace

open Classical in
theorem surfaceEulerCount_ne_two_of_rim_retraction
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (gamma : C(sphere (0 : Fin 2 → ℝ) 1, K.space))
    (radial : C(K.space, sphere (0 : Fin 2 → ℝ) 1))
    (hleft : ∀ u, radial (gamma u) = u) : K.surfaceEulerCount ≠ 2 := by
  intro hcount
  let : SimplyConnectedSpace K.space :=
    K.simplyConnectedSpace_of_surfaceEulerCount_eq_two hK hpure hconn hlinks hcofaces hcount
  apply PoincareConjecture.M76.Dehn.squareRimLoop_map_class_ne_one_of_retraction gamma radial hleft
  exact Path.Homotopic.Quotient.eq.mpr (SimplyConnectedSpace.paths_homotopic _ _)

open Classical in
theorem closed_surface_rank_ge_two_of_rim_retraction
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
    (gamma : C(sphere (0 : Fin 2 → ℝ) 1, K.space))
    (radial : C(K.space, sphere (0 : Fin 2 → ℝ) 1))
    (hleft : ∀ u, radial (gamma u) = u) :
    letI : Fintype K.vertices := (K.finite_vertices_of_finite_faces hK).fintype
    let KA := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
    K.surfaceEulerCount ≤ 0 ∧
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary KA)) + 2 ≤
        Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary KA)) := by
  exact K.closed_surface_rank_ge_two_of_geometric_signs hK hpure hconn hlinks hcofaces
    number hnumber sign hcancel
    (K.surfaceEulerCount_ne_two_of_rim_retraction hK hpure hconn hlinks hcofaces
      gamma radial hleft)

end Geometry.SimplicialComplex
