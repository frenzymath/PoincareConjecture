import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Spheres.Systems.TriangleArcGraphPosition
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.AffineTriangleComponents
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.CircleFreeFaceArcs

set_option autoImplicit false
open Set Geometry
namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem InCircleFreeNonreturningTriangleGraphPosition.exists_normal_arc_family
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X]
    (K : SimplicialComplex ℝ E) (g : E → X) (hgi : InjOn g K.space)
    {s : Finset E} (hs : s ∈ K.faces)
    (Q : OpenPartialHomeomorph X V3) (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    {S : Set X} (hposition : InCircleFreeNonreturningTriangleGraphPosition Q S g s A) :
    ∃ (γ : Type) (_ : Finite γ) (d r : γ → Set V3),
      (Pairwise fun i j => Disjoint (d i) (d j)) ∧
      Q.symm '' (⋃ i, d i) = S ∩ (g '' convexHull ℝ (s : Set E)) ∧
      (⋃ i, d i) ⊆ convexHull ℝ (A '' (s : Set E)) ∩ Q.target ∧
      ∀ i, IsFinitePLBallPair ℝ (d i) (r i) ∧
        r i = d i ∩ intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E))) ∧
        ∀ a : Finset E, a ⊆ s → a.card = 2 →
          ¬ r i ⊆ convexHull ℝ (A '' (a : Set E)) := by
  classical
  obtain ⟨G, hG, hGT, hdim, hphysical, hint, hext, hfinite,
    _, hreturn, hboundary⟩ := hposition
  let t := s.image A
  have ht : t.Nonempty := Finset.image_nonempty.mpr (K.nonempty_of_mem_faces hs)
  have hind : AffineIndependent ℝ ((↑) : t → V3) := by
    change AffineIndependent ℝ ((↑) : ↥((s.image A : Finset V3) : Set V3) → V3)
    rw [Finset.coe_image]
    exact affineIndependent_original_face_chart K g hgi hs Q A hmap hA
  have htset : (t : Set V3) = A '' (s : Set E) := Finset.coe_image
  obtain ⟨hcarrier, hdis, harcs⟩ := G.exists_actual_circle_free_face_arcs hG hdim
    t ht hind (by simpa only [htset] using hGT.trans inter_subset_left)
    (by simpa only [htset] using hfinite)
    (by simpa only [htset] using hint) (by simpa only [htset] using hext)
    (by simpa only [htset] using hboundary)
  let γ := G.vertexAbstractComplex.edgeGraph.ConnectedComponent
  let d : γ → Set V3 := fun C => C.toSimpleGraph.segmentCarrier (fun v => (v.val : V3))
  let r : γ → Set V3 := fun C => d C ∩
    intrinsicFrontier ℝ (convexHull ℝ (A '' (s : Set E)))
  let : Finite G.vertices := (G.finite_vertices_of_finite_faces hG).to_subtype
  refine ⟨γ, inferInstance, d, r, hdis, hcarrier ▸ hphysical, hcarrier ▸ hGT, ?_⟩
  intro C
  obtain ⟨n, e, _, hball, _, _⟩ := harcs C
  refine ⟨by simpa only [htset] using hball, rfl, ?_⟩
  intro a ha hac hsub
  have hfront : r C = Subtype.val '' {v : G.vertices | v ∈ C.supp ∧
      (G.vertexAbstractComplex.edgeGraph.neighborSet v).ncard = 1} := by
    simpa only [htset] using G.actual_component_frontier_eq_degree_one_vertices
      hdim t ht hind (by simpa only [htset] using hGT.trans inter_subset_left)
      (by simpa only [htset] using hfinite)
      (by simpa only [htset] using hint) (by simpa only [htset] using hext) C
  obtain ⟨x, hx⟩ := hboundary C
  obtain ⟨v, hv, _⟩ := hfront.subset hx
  exact hreturn a ha hac ⟨C, ⟨⟨v, hv.1⟩, hv.2⟩, hfront ▸ hsub⟩

end PoincareConjecture.M76
