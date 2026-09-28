import PoincareConjecture.Proofs.M76.Wall.Mathlib.ComponentSphereFromCount
import PoincareConjecture.Proofs.M76.Wall.OriginalFinitePLSphereImage











set_option autoImplicit false

open Set Geometry PreAbstractSimplicialComplex.ModTwoCochains

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)





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

end PoincareConjecture.M76
