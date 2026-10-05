import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Contacts.IntervalGerms
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.OriginalContactLineCover
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Graphs.FinitePLIntervalGerm
import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Arcs.FinitePLIntervals

/-!
# Full two-segment germs near original triangle-edge contacts

A finite PL chart transition transports a closed part of the constructed
half-interval. Every nearby point except its original endpoint is an
interior point of this actual PL interval. Its full two-segment germ
therefore describes the entire original sphere/triangle intersection.
See PrimeReduction034, sections 2--5, and Hudson 1969, pp. 15--19.
-/

set_option autoImplicit false

open Set Geometry Filter
open scoped Topology

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- Every point other than the original endpoint, sufficiently near an
original triangle-edge contact in any compatible chart, has the full
two-segment germ of the entire sphere/triangle intersection. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_two_segment_germs_in_chart
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
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_contact_two_segment_germs_in_chart sS.chart_source_cover hgi hSV hpq hwp
    hwq ht hy Q hQ hyQ

/-- In the original whole-face affine coordinates, all nearby points
except the old contact have the full two-segment germ of the complete
sphere/affine-triangle intersection. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_two_segment_germs_of_affine_chart
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
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U,
        x ≠ Q y → ∃ u v : V3, u ≠ x ∧ v ≠ x ∧
          segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_contact_two_segment_germs_of_affine_chart sS.chart_source_cover hgi hSV
    hpq hwp hwq ht hy Q hQ A hmap hA

/-- The original data alone supply two-segment germs at all nearby
sphere contacts in the relative interior of the whole affine triangle.
The original edge endpoint is excluded by the simplicial intersection law. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_interior_two_segment_germs_of_affine_chart
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
    (A : E →ᴬ[ℝ] V3)
    (hmap : MapsTo g (convexHull ℝ ({w, p, q} : Set E)) Q.source)
    (hA : EqOn (Q ∘ g) A (convexHull ℝ ({w, p, q} : Set E))) :
    ∃ U : Set V3, IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
          intrinsicInterior ℝ (convexHull ℝ (A '' ({w, p, q} : Set E)))) ∩ U,
        ∃ u v : V3, u ≠ x ∧ v ≠ x ∧ segment ℝ x u ∩ segment ℝ x v ⊆ {x} ∧
          ∀ᶠ a in 𝓝 x,
            a ∈ Q '' (S ∩ Q.source) ∩ convexHull ℝ (A '' ({w, p, q} : Set E)) ↔
              a ∈ segment ℝ x u ∪ segment ℝ x v := by
  exact h.exists_surface_interior_two_segment_germs_of_affine_chart sS.chart_source_cover hgi hSV
    hpq hwp hwq ht hy Q hQ A hmap hA

end PoincareMT.M76
