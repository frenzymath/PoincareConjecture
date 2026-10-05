import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.Systems.NormalFaceArcFamily
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.OriginalTriangleEndpoint
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Regions.FinitePLIntervalBoundary

/-!
# Normal arcs join the interiors of distinct original edges

The exact two-point rim of each constructed PL interval lies on the
triangle frontier. Vertex protection puts both points inside original
edges; nonreturning forces those two edges to be distinct.
-/

set_option autoImplicit false
open Set Geometry
namespace PoincareMT.M76
local notation "V3" => (Fin 3 → ℝ)

theorem InCircleFreeNonreturningTriangleGraphPosition.exists_normal_arc_family_with_endpoints
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hSV : Disjoint S (g '' K.vertices))
    (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set V3),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      Q.symm '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      ∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) ∧
        ∃ (x y : V3) (a b : Finset E), x ≠ y ∧ r i = {x, y} ∧
          a ⊆ s ∧ a.card = 2 ∧ b ⊆ s ∧ b.card = 2 ∧ a ≠ b ∧
          x ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (a : Set E))) ∧
          y ∈ intrinsicInterior ℝ (convexHull ℝ (A '' (b : Set E))) := by
  obtain ⟨γ, hγ, d, r, hdis, hphysical, htarget, harcs⟩ :=
    hposition.exists_normal_arc_family K g hgi hs Q A hmap hA
  refine ⟨γ, hγ, d, r, hdis, hphysical, htarget, fun i => ?_⟩
  obtain ⟨hball, hrim, hreturn⟩ := harcs i
  obtain ⟨x, y, hxy, hpair⟩ := hball.exists_boundary_eq_pair
  have hx : x ∈ r i := hpair.symm ▸ (show x ∈ ({x, y} : Set V3) by simp)
  have hy : y ∈ r i := hpair.symm ▸ (show y ∈ ({x, y} : Set V3) by simp)
  have hpoint {z : V3} (hz : z ∈ r i) : Q.symm z ∈ S :=
    (hphysical.subset ⟨z, mem_iUnion.mpr ⟨i, hball.1 hz⟩, rfl⟩).1
  obtain ⟨a, ha, hac, hxa⟩ := exists_original_edge_interior_of_triangle_frontier
    K g hgi hSV hs hs3 Q A hmap hA (hpoint hx) (hrim.subset hx).2
  obtain ⟨b, hb, hbc, hyb⟩ := exists_original_edge_interior_of_triangle_frontier
    K g hgi hSV hs hs3 Q A hmap hA (hpoint hy) (hrim.subset hy).2
  have hab : a ≠ b := by
    intro heq
    apply hreturn a ha hac
    rw [hpair]
    rintro z (rfl | rfl)
    · exact intrinsicInterior_subset hxa
    · exact intrinsicInterior_subset (heq.symm ▸ hyb)
  exact ⟨hball, hrim, x, y, a, b, hxy, hpair, ha, hac, hb, hbc, hab, hxa, hyb⟩

end PoincareMT.M76
