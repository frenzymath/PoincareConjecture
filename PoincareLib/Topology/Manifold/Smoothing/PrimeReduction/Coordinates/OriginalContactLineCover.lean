import PoincareLib.Topology.Manifold.Smoothing.Rigidity.Products.FailureArc.Intersections.Position.Contacts.LineCover
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Simplicial.OriginalContactGraph
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Spheres.OriginalSphereChartCarrier
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Affine.AffineContactFiniteness
import PoincareLib.Topology.Manifold.Smoothing.Dehn.Simplicial.Mathlib.FreeFaceCarrierBounds

/-!
# Original contact line covers in another compatible chart

The original half-interval constructs a complete finite contact graph.
One atlas chart through the sphere point provides an actual PL overlap
between its edge chart and any requested compatible chart. Transport the
graph on a finite transition patch and retain all intersection points in
an open target neighborhood. No global atlas coverage is used.
See PrimeReduction034, sections 2--5, and Hudson 1969, pp. 15--19.
-/

set_option autoImplicit false

open Set Geometry Module

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- Original edge-contact data construct a finite line cover of the
complete sphere/triangle intersection near the contact in any compatible
chart containing it. Only one original chart through the sphere point is
used to transfer the constructed half-interval graph. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_line_cover_in_chart
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
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ A ∈ L, finrank ℝ A.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ (g '' convexHull ℝ ({w, p, q} : Set E)) ∩ Q.source)) ∩ U,
        ∃ A ∈ L, x ∈ A := by
  exact h.exists_surface_contact_line_cover_in_chart sS.chart_source_cover hgi hSV hpq hwp hwq ht
    hy Q hQ hyQ

/-- In a whole-face affine chart, the original contact supplies a local
finite line cover of the full sphere-coordinate image intersected with
the complete affine target triangle. -/
theorem HasOriginalEdgeCofaceCharts.exists_triangle_contact_line_cover_of_affine_chart
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
    ∃ (U : Set V3) (L : Finset (AffineSubspace ℝ V3)),
      IsOpen U ∧ Q y ∈ U ∧ U ⊆ Q.target ∧
      (∀ B ∈ L, finrank ℝ B.direction ≤ 1) ∧
      ∀ x ∈ (Q '' (S ∩ Q.source) ∩
        convexHull ℝ (A '' ({w, p, q} : Set E))) ∩ U, ∃ B ∈ L, x ∈ B := by
  exact h.exists_surface_contact_line_cover_of_affine_chart sS.chart_source_cover hgi hSV hpq hwp
    hwq ht hy Q hQ A hmap hA

end PoincareMT.M76
