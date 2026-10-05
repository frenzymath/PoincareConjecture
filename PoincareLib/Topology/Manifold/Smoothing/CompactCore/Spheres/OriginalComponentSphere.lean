import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.Mathlib.ComponentSphereFromCount
import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Spheres.OriginalFinitePLSphereImage

/-!
# The whole original component sphere from the literal zero count

Construct the finite PL model of the unchanged whole component from
its exact count, then return it through the original chartwise PL
inverse. The complete original image is the sphere carrier.
See Hudson 1969, pp. 12--19, Putman, Theorem 5.1, pp. 15--16,
and Wall017, section 3.
-/

set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)

/-- The literal zero count for one whole boundary component gives
its actual original chartwise PL sphere. The original inverse, whole
surface incidence and exact count are retained explicitly; no terminal
tower premise is used. See Wall017, section 3. -/
theorem exists_original_component_sphere_of_count
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [DecidableEq E] [TopologicalSpace X] [T2Space X]
    {e : ι → OpenPartialHomeomorph X V3}
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    {g : E → X} (hg : PolyhedralPLInCharts e g K.space) (hgi : InjOn g K.space)
    (hpure : ∀ s ∈ A.faces, ∃ t ∈ A.faces, s ⊆ t ∧ t.card = 3)
    (hcofaces : ∀ s ∈ A.faces, s.card = 2 →
      {t : Finset E | t ∈ A.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ A.vertices, IsConnected (A.faceLink {p}).space)
    (C : A.vertexAbstractComplex.edgeGraph.ConnectedComponent)
    (hcount : Nat.card (A.edgeComponentComplex C).vertices +
      Nat.card (Triangle
        (A.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) =
      Nat.card (Edge
        (A.edgeComponentComplex C).vertexAbstractComplex.toPreAbstractSimplicialComplex) + 2) :
    Nonempty (ChartwisePLSphere e (g '' (A.edgeComponentComplex C).space)) := by
  obtain ⟨b, hb⟩ := A.exists_edgeComponent_cube_sphere_of_count
    (hK.subset hAK) C hpure hcofaces hlinks hcount
  exact exists_chartwisePLSphere_image K hg hgi
    (SimplicialComplex.space_subset_of_le ((A.edgeComponentComplex_le C).trans hAK)) b hb

end PoincareMT.M76
