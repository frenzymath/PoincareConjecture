import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Contacts.Endpoints
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.OriginalContactLineCover
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLIntervals

/-!
# Degree one at the original boundary contacts in another chart

Transport a closed initial interval of the original half-interval through
an actual finite PL transition patch. Its endpoint supplies the complete
half-segment germ and hence degree one in any finite carrier agreeing
locally with the full physical sphere/triangle intersection.
See PrimeReduction034, sections 2--5, and Hudson 1969, pp. 15--19.
-/

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The old endpoint has the complete nondegenerate half-segment germ
in any compatible chart containing it. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_segment_germ_in_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {p q w : E}
    (h : HasOriginalEdgeCofaceCharts e S K g {p, q})
    (sS : ChartwisePLSphere e S)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    (hpq : p ≠ q) (hwp : w ≠ p) (hwq : w ≠ q)
    (ht : ({w, p, q} : Finset E) ∈ K.faces)
    {y : X} (hy : y ∈ S ∩ (g '' segment ℝ p q))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (hyQ : y ∈ Q.source) :
    ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) ↔
        x ∈ segment ℝ (Q y) u := by
  exact h.exists_surface_contact_segment_germ_in_chart sS.chart_source_cover hgi hSV hpq hwp hwq
    ht hy Q hQ hyQ

/-- In the unchanged whole-face affine chart, the complete old
sphere/triangle intersection has a half-segment germ at its edge contact. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_segment_germ_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (sS : ChartwisePLSphere e S) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E)))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E))) :
    ∃ u : V3, u ≠ Q y ∧ ∀ᶠ x in 𝓝 (Q y),
      x ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E)) ↔
        x ∈ segment ℝ (Q y) u := by
  exact h.exists_surface_contact_segment_germ_of_affine_chart sS.chart_source_cover hs hs3 has ha2
    hgi hSV hy Q hQ A hmap hA

/-- Every finite carrier with the full original contact germ has degree
one at the marked contact. It can be the moved graph whenever the old
sphere germ has been preserved there. -/
theorem HasOriginalEdgeCofaceCharts.ncard_contact_neighborSet_eq_one_of_affine_chart
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S : Set X}
    {K : SimplicialComplex ℝ E} {g : E → X} {s a : Finset E}
    (h : HasOriginalEdgeCofaceCharts e S K g a)
    (sS : ChartwisePLSphere e S) (hs : s ∈ K.faces) (hs3 : s.card = 3)
    (has : a ⊆ s) (ha2 : a.card = 2)
    (hgi : InjOn g K.space) (hSV : Disjoint S (g '' K.vertices))
    {y : X} (hy : y ∈ S ∩ (g '' convexHull ℝ (a : Set E)))
    (Q : OpenPartialHomeomorph X V3)
    (hQ : ∀ i, (e i).symm.trans Q ∈ piecewiseAffineGroupoid V3)
    (A : E →ᴬ[ℝ] V3) (hmap : MapsTo g (convexHull ℝ (s : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ (s : Set E)))
    (G : SimplicialComplex ℝ V3) (hG : G.faces.Finite) (hyG : Q y ∈ G.vertices)
    (hlocal : ∀ᶠ x in 𝓝 (Q y), x ∈ G.space ↔
      x ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' (s : Set E))) :
    (G.vertexAbstractComplex.edgeGraph.neighborSet ⟨Q y, hyG⟩).ncard = 1 := by
  exact h.ncard_surface_contact_neighborSet_eq_one_of_affine_chart sS.chart_source_cover hs hs3
    has ha2 hgi hSV hy Q hQ A hmap hA G hG hyG hlocal

end PoincareMT.M76
