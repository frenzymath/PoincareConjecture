import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Surfaces.OriginalTorusEuler
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Topology.Mathlib.SurfaceEulerValuation
import PoincareLib.Topology.Manifold.Smoothing.Rigidity.IndexOne.Topology.CircleGroups.CharacterKernel
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Annuli.Surfaces.Cuts.EssentialClosedComponent

/-!
# Rank arithmetic for an incompressible oriented finite surface

The finite surface is kept as the actual simplicial complex.  A three
coordinate mod-two character map is the cohomology/fundamental-group bridge:
its kernel consists of vertex coboundaries.  The linear-algebra argument below
then proves the closed-cochain rank bound, Euler zero, and the residual-two
producer.  No surface classification or pre-packaged Euler certificate is
used.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains
open PoincareMT.M76.Dehn
open AbstractSimplicialComplex

namespace PoincareMT.M76

/- The rank of the actual closed cochains is at most the vertex coboundaries
  plus the three ambient mod-two coordinates. -/
theorem finrank_closed_le_finrank_coboundaries_add_three
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E]
    {K : SimplicialComplex ℝ E} [Fintype K.vertices]
    (eval : LinearMap.ker (edgeCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex) →ₗ[ZMod 2]
        (Fin 3 → ZMod 2))
    (T : LinearMap.ker eval →ₗ[ZMod 2] LinearMap.range (vertexCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hT : Function.Injective T) :
    Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) ≤
      Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 3 := by
  let A := K.vertexAbstractComplex.toPreAbstractSimplicialComplex
  have hdim := LinearMap.finrank_range_add_finrank_ker (K := ZMod 2) eval
  have hkerdim := LinearMap.finrank_le_finrank_of_injective hT
  have hrange := (LinearMap.range eval).finrank_le
  have hcodim : Module.finrank (ZMod 2) (Fin 3 → ZMod 2) ≤ 3 := by
    norm_num [Module.finrank_pi]
  omega

/- The actual closed oriented surface has Euler characteristic zero once its
  closed cochains admit at most three independent ambient characters. -/
open Classical in
theorem surfaceEulerCount_eq_zero_of_character_rank
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K : SimplicialComplex ℝ E) [Fintype K.vertices] (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hconn : IsConnected K.space)
    (hlinks : ∀ v ∈ K.vertices, IsConnected (K.link v).space)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (number : E → ℕ) (hnumber : InjOn number K.vertices)
    (sign : Finset E → ZMod 2)
    (hcancel : ∀ t ∈ K.faces, t.card = 3 → ∀ u ∈ K.faces, u.card = 3 →
      t ≠ u → ∀ s : Finset E, s.card = 2 → s ⊆ t → s ⊆ u →
        (sign t + boundaryFaceParity number t s) +
          (sign u + boundaryFaceParity number u s) = 1)
    (x : K.space) [Nontrivial (FundamentalGroup K.space x)]
    (eval : LinearMap.ker (edgeCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex) →ₗ[ZMod 2]
        (Fin 3 → ZMod 2))
    (T : LinearMap.ker eval →ₗ[ZMod 2] LinearMap.range (vertexCoboundary
      K.vertexAbstractComplex.toPreAbstractSimplicialComplex))
    (hT : Function.Injective T) :
    K.surfaceEulerCount = 0 := by
  have hbound := finrank_closed_le_finrank_coboundaries_add_three eval T hT
  have hidentity := K.closed_surface_incidence_rank_identity hK hpure hconn hlinks
    hcofaces
  have hne : K.surfaceEulerCount ≠ 2 := by
    intro htwo
    letI : SimplyConnectedSpace K.space :=
      K.simplyConnectedSpace_of_surfaceEulerCount_eq_two hK hpure hconn hlinks
        hcofaces htwo
    exact not_nontrivial (FundamentalGroup K.space x) inferInstance
  have hnonpos := (K.closed_surface_rank_ge_two_of_geometric_signs hK hpure hconn
    hlinks hcofaces number hnumber sign hcancel hne).1
  have hparity := K.even_surfaceEulerCount_of_geometric_signs hK hpure hlinks
    hcofaces number hnumber sign hcancel
  have hlower : (-1 : ℤ) ≤ K.surfaceEulerCount := by
    have hbound' :
        (Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary
          K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) : ℤ) ≤
          Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary
            K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) + 3 := by
      exact_mod_cast hbound
    have hf : (inferInstance : Fintype K.vertices) =
        (K.finite_vertices_of_finite_faces hK).fintype := Subsingleton.elim _ _
    have hidentity' : K.surfaceEulerCount +
        (Module.finrank (ZMod 2) (LinearMap.ker (edgeCoboundary
          K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) : ℤ) =
      (Module.finrank (ZMod 2) (LinearMap.range (vertexCoboundary
        K.vertexAbstractComplex.toPreAbstractSimplicialComplex)) : ℤ) + 2 := by
      cases hf
      simpa only using hidentity
    omega
  rcases hparity with ⟨k, hk⟩
  omega

/- The rank theorem consumes the same residual equation stored by the actual
  frontier model, so the residual-two conclusion is not a separate supplier. -/
theorem FrontierResidualModel.residual_eq_two_of_character_rank
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N F : Set X}
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (hzero : (M.complex.edgeComponentComplex (M.pick i)).surfaceEulerCount = 0) :
    M.residual i = 2 := by
  have h := M.euler i
  rw [hzero] at h
  omega

theorem FrontierResidualModel.original_torus_candidate_of_character_rank
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X (Fin 3 → ℝ)} {N F : Set X}
    (M : FrontierResidualModel e N F) (i : Fin M.count)
    (hzero : (M.complex.edgeComponentComplex (M.pick i)).surfaceEulerCount = 0) :
    ∃ T : OriginalTorusEulerCandidate e N F,
      T.model = M ∧ (T.componentComplex).surfaceEulerCount = 0 := by
  have hres := M.residual_eq_two_of_character_rank i hzero
  let T : OriginalTorusEulerCandidate e N F := ⟨M, i, hres⟩
  exact ⟨T, rfl, hzero⟩

end PoincareMT.M76
