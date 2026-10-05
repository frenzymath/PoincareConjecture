import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.AffineTriangleComponents
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Simplicial.SimplexIntrinsicFrontier

/-!
# Vertex-protected endpoints on original triangle edges

A section point on a triangle frontier belongs to an original edge.
Avoidance of the original vertex images puts it in that edge's full
intrinsic interior.
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)

theorem exists_original_edge_interior_of_triangle_frontier
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {S : Set X} (hSV : Disjoint S (g '' K.vertices))
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {x : V3} (hxS : Q.symm x ∈ S)
    (hxf : x ∈ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))) :
    ∃ a : Finset E, a ⊆ s ∧ a.card = 2 ∧
      x ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E))) := by
  classical
  have hAi : InjOn A (s : Set E) := by
    intro u hu v hv heq
    have hu' := subset_convexHull ℝ (s : Set E) hu
    have hv' := subset_convexHull ℝ (s : Set E) hv
    exact hgi (K.convexHull_subset_space hs hu') (K.convexHull_subset_space hs hv')
      (Q.injOn (hmap hu') (hmap hv') ((hA hu').trans (heq.trans (hA hv').symm)))
  have hxnot : x ∉ s.image A := by
    rintro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx
    have hu' := subset_convexHull ℝ (s : Set E) hu
    have hQAu : Q.symm (A u) = g u := by
      rw [← hA hu']
      exact Q.left_inv (hmap hu')
    exact Set.disjoint_left.mp hSV (hQAu ▸ hxS)
      ⟨u, K.face_subset_vertices hs hu, rfl⟩
  have hind : AffineIndependent ℝ ((↑) : (s.image A) → V3) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
    rw [Finset.coe_image]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have htne : (s.image A).Nonempty := Finset.image_nonempty.mpr (K.nonempty_of_mem_faces hs)
  obtain ⟨v, hv, hxv⟩ := (hind.mem_intrinsicFrontier_convexHull_finset htne x).mp
    (by simpa only [Finset.coe_image] using hxf)
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hv
  let a := s.erase u
  have hac : a.card = 2 := by simp [a, Finset.card_erase_of_mem hu, hs3]
  have haim : a.image A = (s.image A).erase (A u) := by
    ext y
    constructor
    · rintro hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      have hz' := Finset.mem_erase.mp hz
      exact Finset.mem_erase.mpr ⟨fun heq => hz'.1 (hAi hz'.2 hu heq),
        Finset.mem_image.mpr ⟨z, hz'.2, rfl⟩⟩
    · intro hy
      obtain ⟨hne, hy⟩ := Finset.mem_erase.mp hy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr
        ⟨fun hzu => hne (congrArg A hzu), hz⟩, rfl⟩
  have hxa : x ∈ convexHull ℝ ((a.image A : Finset V3) : Set V3) := by
    rwa [haim]
  have haind : AffineIndependent ℝ ((↑) : (a.image A) → V3) :=
    hind.mono (Finset.coe_subset.mpr (Finset.image_subset_image (Finset.erase_subset _ _)))
  have hac' : (a.image A).card = 2 :=
    (Finset.card_image_of_injOn (hAi.mono (Finset.erase_subset _ _))).trans hac
  refine ⟨a, Finset.erase_subset _ _, hac, ?_⟩
  rw [← Finset.coe_image]
  by_contra hnot
  have hfront : x ∈ intrinsicFrontier ℝ (convexHull ℝ ((a.image A : Finset V3) : Set V3)) := by
    rw [← intrinsicClosure_sdiff_intrinsicInterior]
    exact ⟨subset_intrinsicClosure hxa, hnot⟩
  obtain ⟨w, hw, hxw⟩ := (haind.mem_intrinsicFrontier_convexHull_finset
    (Finset.card_pos.mp (by omega)) x).mp hfront
  have hcard : ((a.image A).erase w).card = 1 := by
    rw [Finset.card_erase_of_mem hw, hac']
  obtain ⟨z, hz⟩ := Finset.card_eq_one.mp hcard
  have hxz : x = z := by simpa only [hz, Finset.coe_singleton,
    convexHull_singleton, mem_singleton_iff] using hxw
  apply hxnot
  rw [hxz]
  exact (Finset.image_subset_image (Finset.erase_subset u s))
    (Finset.mem_of_mem_erase (show z ∈ (a.image A).erase w by rw [hz]; simp))

end PoincareMT.M76
