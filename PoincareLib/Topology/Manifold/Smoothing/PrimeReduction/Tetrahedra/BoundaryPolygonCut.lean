import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Tetrahedra.OriginalTetrahedronBall
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Spheres.PLSpherePolygonCut
import PoincareLib.Topology.Manifold.Smoothing.Triangulation.Affine.ConvexSphereLargeDisks
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLBallNormalization
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Regions.PunctureBallTriangulation

/-!
# Exact polygon cuts on the original tetrahedron boundary

The intrinsic tetrahedron ball constructs its whole finite PL sphere chart.
Polygon cuts and compact vertex-avoiding disks are transported through that
chart, retaining their literal original carriers. See Kneser 1929, p. 255.
-/

set_option autoImplicit false
open Set Metric Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

private theorem exists_independent_tetrahedron_boundary_chart
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 4) :
    ∃ H : intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ≃ₜ
      frontier (closedBall (0 : V3) 1), H.IsFinitePL := by
  have hball := isFinitePLBallPair_independent_tetrahedron s hind hcard
  obtain ⟨G,hG,hGb⟩ := hball.exists_cube_chart (ContinuousLinearEquiv.refl ℝ V3)
  obtain ⟨_,K,_,_,hK,hKs⟩ := hball.exists_finite_carrier_and_rim_complexes
  exact ⟨G.restrictSubsets hball.1 isClosed_closedBall.frontier_subset hGb,
    hG.restrictSubsets hball.1 isClosed_closedBall.frontier_subset hGb K hK hKs⟩

theorem exists_independent_tetrahedron_boundary_polygon_cut
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 4)
    {n : ℕ} (P : Polygon E (n + 3)) (hP : P.HasSimplicialEdges)
    (hPi : Function.Injective P)
    (hPs : P.boundary ℝ ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    {v : E} (hv : v ∈ s) (hvP : v ∉ P.boundary ℝ) :
    ∃ b c : Set E, IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) c (P.boundary ℝ) ∧
      b ∪ c = intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧
      b ∩ c = P.boundary ℝ ∧ v ∈ c \ P.boundary ℝ := by
  obtain ⟨H,hH⟩ := exists_independent_tetrahedron_boundary_chart s hind hcard
  exact hH.exists_polygon_cut (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ (by simp)
    P hP hPi hPs ⟨v,vertex_mem_intrinsicFrontier_independent_tetrahedron s hind hcard hv⟩ hvP

theorem exists_independent_tetrahedron_boundary_disk_of_compact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (s : Finset E) (hind : AffineIndependent ℝ ((↑) : s → E)) (hcard : s.card = 4)
    {a : Set E} (ha : IsCompact a)
    (has : a ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)))
    {v : E} (hv : v ∈ s) (hva : v ∉ a) :
    ∃ d q : Set E, IsFinitePLBallPair (ℝ × ℝ) d q ∧
      d ⊆ intrinsicFrontier ℝ (convexHull ℝ (s : Set E)) ∧ a ⊆ d \ q ∧ v ∉ d := by
  let T := intrinsicFrontier ℝ (convexHull ℝ (s : Set E))
  have hvT : v ∈ T := vertex_mem_intrinsicFrontier_independent_tetrahedron s hind hcard hv
  obtain ⟨H,hH⟩ := exists_independent_tetrahedron_boundary_chart s hind hcard
  have hHcopy := hH
  obtain ⟨f,hf,hfval⟩ := hHcopy
  obtain ⟨g,hg,hgval⟩ := hH.symm
  have hgf : LeftInvOn g f T := by
    intro x hx
    rw [←hfval ⟨x,hx⟩,←hgval,H.symm_apply_apply]
  have hfg : LeftInvOn f g (frontier (closedBall (0 : V3) 1)) := by
    intro x hx
    rw [←hgval ⟨x,hx⟩,←hfval,H.apply_symm_apply]
  have haf : IsCompact (f '' a) := ha.image_of_continuousOn (hf.continuousOn.mono has)
  have hafsub : f '' a ⊆ frontier (closedBall (0 : V3) 1) := by
    rintro _ ⟨x,hx,rfl⟩
    rw [←hfval ⟨x,has hx⟩]
    exact (H ⟨x,has hx⟩).property
  have hp : (H ⟨v,hvT⟩ : V3) ∉ f '' a := by
    rintro ⟨x,hx,hxp⟩
    rw [hfval] at hxp
    exact hva (hgf.injOn (has hx) hvT hxp ▸ hx)
  have hgcopy := hg
  obtain ⟨K,hK,hKs,_⟩ := hgcopy
  obtain ⟨d,q,hd,hds,had,hpd⟩ := K.exists_convex_frontier_disk_of_compact hK
    (isCompact_closedBall _ _) (convex_closedBall _ _)
    ⟨0,ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hKs
    (F := ℝ × ℝ) (by simp [Module.finrank_prod]) (H ⟨v,hvT⟩) haf hafsub hp
  refine ⟨g '' d,g '' q,hd.image_of_subset hg hds hfg.injOn,?_,?_,?_⟩
  · rintro _ ⟨x,hx,rfl⟩
    rw [←hgval ⟨x,hds hx⟩]
    exact (H.symm ⟨x,hds hx⟩).property
  · intro x hx
    have hfx := had (mem_image_of_mem f hx)
    refine ⟨⟨f x,hfx.1,hgf (has hx)⟩,?_⟩
    rintro ⟨y,hy,hyx⟩
    apply hfx.2
    have hfy := congrArg f hyx
    rw [hfg (hds (hd.1 hy))] at hfy
    exact hfy ▸ hy
  · rintro ⟨x,hx,hxv⟩
    apply hpd
    rw [hfval]
    have hfx := congrArg f hxv
    rw [hfg (hds hx)] at hfx
    exact hfx ▸ hx

end PoincareMT.M76
