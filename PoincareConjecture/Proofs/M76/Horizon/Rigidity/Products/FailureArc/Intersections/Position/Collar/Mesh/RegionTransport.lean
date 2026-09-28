import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.PairTransport
import PoincareConjecture.Proofs.M76.Horizon.Rigidity.Products.FailureArc.Intersections.Position.Collar.Mesh.ProtectedVertices

set_option autoImplicit false
open Set Geometry

namespace PoincareConjecture.M76
local notation "V3" => (Fin 3 → ℝ)

theorem OriginalSurfacePairChart.image_first_region_model
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R : Set X} {y : X} {b : Bool}
    (C : OriginalSurfacePairChart e S T y b)
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hT : F ⁻¹' T = T) (hR : F ⁻¹' R = R)
    (A : Set (ℝ × ℝ))
    (hC : ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ (C.coordinates z).1 ∈ A) :
    let D := C.image_first_of_preserving_second hcover F hFinv hT
    ∀ z ∈ D.coordinates.source, D.chart.symm z ∈ R ↔ (D.coordinates z).1 ∈ A := by
  intro D z hz
  change F (C.chart.symm z) ∈ R ↔ (C.coordinates z).1 ∈ A
  have hmem : F (C.chart.symm z) ∈ R ↔ C.chart.symm z ∈ R := by
    change C.chart.symm z ∈ F ⁻¹' R ↔ _
    rw [hR]
  exact hmem.trans (hC z hz)

theorem region_pair_chart_image_of_preserving_sets
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {S T R : Set X}
    (hcover : ∀ x, ∃ i, x ∈ (e i).source)
    (F : X ≃ₜ X)
    (hFinv : ∀ i j, (e i).symm.trans (F.symm.toOpenPartialHomeomorph.trans (e j)) ∈
      piecewiseAffineGroupoid V3)
    (hT : F ⁻¹' T = T) (hR : F ⁻¹' R = R)
    {y : X}
    (hchart :
      (y ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e S T y false)) ∨
      ∃ C : OriginalSurfacePairChart e S T y true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2) :
    (F y ∈ interior R ∧ Nonempty (OriginalSurfacePairChart e (F '' S) T (F y) false)) ∨
      ∃ C : OriginalSurfacePairChart e (F '' S) T (F y) true,
        ∀ z ∈ C.coordinates.source, C.chart.symm z ∈ R ↔ 0 ≤ (C.coordinates z).1.2 := by
  rcases hchart with ⟨hyR, ⟨C⟩⟩ | ⟨C, hC⟩
  · refine Or.inl ⟨?_, ⟨C.image_first_of_preserving_second hcover F hFinv hT⟩⟩
    change y ∈ F ⁻¹' interior R
    rwa [F.preimage_interior, hR]
  · exact Or.inr ⟨C.image_first_of_preserving_second hcover F hFinv hT,
      C.image_first_region_model hcover F hFinv hT hR {v | 0 ≤ v.2} hC⟩

end PoincareConjecture.M76
