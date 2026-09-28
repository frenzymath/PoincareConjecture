import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Contacts.Endpoints
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Coordinates.OriginalContactLineCover
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.Graphs.FinitePLIntervalEndpoint
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLIntervals

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)

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

end PoincareConjecture.M76
