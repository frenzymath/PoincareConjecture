import PoincareLib.Topology.Manifold.Smoothing.Dehn.Spheres.OriginalStageBoundarySpheres
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Disks.Mathlib.SurfacePolygonDisk

/-!
# The actual polygon disk on the original terminal boundary

The unchanged terminal stage and whole marked boundary construct
surface purity and the sphere model. The polygon cut therefore
produces two actual disk pairs on the same complete component.
No surface, outside-point or disk supplier is an additional premise.
See Stallings p. 11 and Dehn derivation 025, sections 1--2.
-/

set_option autoImplicit false

universe u v w z

open Set Geometry

namespace Geometry.OriginalPLTower

local notation "V3" => (Fin 3 → ℝ)

variable {U : Type u} {G : Type v} {M : Type w} {ι : Type z}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [DecidableEq G] [TopologicalSpace M]
  {e : ι → OpenPartialHomeomorph M V3} {S : SimplicialComplex ℝ U}
  {f : U → M} {r : M → ℝ} {C : Set M}

/-- A simple polygon in a whole original terminal boundary
component bounds an actual finite PL disk pair there. The same
original stage constructs the surface and sphere hypotheses and
the actual outside point. See Stallings p. 11 and Dehn025. -/
theorem Stage.relative_region_polygon_disks (st : Stage e S f r C)
    {R : Set M} {N : Set st.Carrier} (hN : IsClosed N)
    (hDN : st.sourceMap '' S.space ⊆ N) (hNR : N ⊆ st.projection ⁻¹' R)
    {u : U} (hu : u ∈ S.space) (hfu : f u ∈ frontier R)
    (a : C(N, N))
    (H : (ContinuousMap.id N).HomotopyRel a (Subtype.val ⁻¹' (st.sourceMap '' S.space)))
    (ha : range a = Subtype.val ⁻¹' (st.sourceMap '' S.space))
    (K : SimplicialComplex ℝ G) (hK : K.faces.Finite)
    (A : SimplicialComplex ℝ G) (hAK : A ≤ K)
    (hfull : ∀ s ∈ K.faces, (∀ p ∈ s, p ∈ A.vertices) → s ∈ A.faces)
    (J : N ≃ₜ K.space) (F : st.Carrier → G) (g : G → N)
    (hJF : ∀ x : N, (J x : G) = F x)
    (hg : ∀ z : K.space, (g z : st.Carrier) = (J.symm z : st.Carrier))
    (hAs : A.space = F '' frontier N)
    (hstars : ∀ p ∈ K.vertices, ∃ B : OpenPartialHomeomorph st.Carrier V3,
      MapsTo (fun z => (g z : st.Carrier)) (K.closedStar p).space B.source ∧
      (K.closedStar p).AffineOnFaces (fun z => B (g z)) ∧
      (B.source ⊆ N ∨ ∃ (ell : V3 →ᴬ[ℝ] ℝ) (v : V3),
        ell.contLinear v = 1 ∧ ∀ y ∈ B.source, y ∈ N ↔ 0 ≤ ell (B y)))
    (hterminal : ∀ (Y : Type (max w v)) [TopologicalSpace Y]
      [T2Space Y] [ConnectedSpace Y] (p : Y → st.Carrier),
      IsCoveringMap p → (∀ x, (p ⁻¹' {x}).ncard = 2) → False)
    (c : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    {n : ℕ} (P : Polygon G (n + 3)) (hP : P.HasSimplicialEdges)
    (hinj : Function.Injective P)
    (hPA : P.boundary ℝ ⊆ (A.edgeComponentComplex c).space) :
    ∃ b d : Set G, IsFinitePLBallPair (ℝ × ℝ) b (P.boundary ℝ) ∧
      IsFinitePLBallPair (ℝ × ℝ) d (P.boundary ℝ) ∧
      b ∪ d = (A.edgeComponentComplex c).space ∧ b ∩ d = P.boundary ℝ := by
  classical
  have hboundary (x : G) (hx : x ∈ K.space) :
      (g x : st.Carrier) ∈ frontier N ↔ x ∈ A.space := by
    rw [hAs]
    exact PoincareMT.M76.original_model_mem_image_iff J F g hJF hg
      hN.frontier_subset ⟨x, hx⟩
  obtain ⟨hpure, _, _⟩ := PoincareMT.M76.original_boundary_surface_incidence
    K A hK hAK hN.frontier_subset J g hg hboundary hstars
  obtain ⟨L, hL⟩ := st.relative_region_boundary_spheres hN hDN hNR hu hfu a H ha
    K hK A hAK hfull J F g hJF hg hAs hstars hterminal c
  exact (A.edgeComponentComplex c).exists_roof_sphere_polygon_disks
    (A.edgeComponentComplex_pure c hpure) L hL P hP hinj hPA

end Geometry.OriginalPLTower
