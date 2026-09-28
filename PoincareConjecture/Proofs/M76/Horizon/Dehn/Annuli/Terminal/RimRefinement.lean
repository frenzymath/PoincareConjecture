import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.SubdivisionStars
import PoincareConjecture.Proofs.M76.Dehn.Mathlib.SquareRimPolygon
import PoincareConjecture.Proofs.M76.Mathlib.PolygonFinitePLImage

set_option autoImplicit false

open Set Metric Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_refinement_with_embedded_rim
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (γ : V2 → E) (hγ : FinitePiecewiseAffineOn γ Q2)
    (hinj : InjOn γ Q2) (hγK : MapsTo γ Q2 K.space) :
    ∃ (R B L : SimplicialComplex ℝ E) (n : ℕ) (P : Polygon E (n + 3)),
      R.faces.Finite ∧ R.IsSubdivision K ∧ B ≤ R ∧ B.space = A.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ B.vertices) → s ∈ B.faces) ∧
      L ≤ R ∧ L.space = γ '' Q2 ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ L.vertices) → s ∈ L.faces) ∧
      P.HasSimplicialEdges ∧ Function.Injective P ∧ P.boundary ℝ = L.space := by
  classical
  obtain ⟨n, P, hPi, hP, hPs⟩ := squareRimPolygon.exists_polygon_finitePL_image
    hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon hγ
    boundary_squareRimPolygon.subset (boundary_squareRimPolygon.symm ▸ hinj)
  have hPimage : P.boundary ℝ = γ '' Q2 := by rwa [boundary_squareRimPolygon] at hPs
  let C := P.simplicialComplex hP
  have hC : C.faces.Finite := P.finite_simplicialComplex_faces hP
  have hCs : C.space = γ '' Q2 := (P.simplicialComplex_space hP).trans hPimage
  let marks : Bool → SimplicialComplex ℝ E := fun b => if b then C else A
  have hmarks (b : Bool) : (marks b).faces.Finite := by
    cases b
    · exact hK.subset hAK
    · exact hC
  have hsub (b : Bool) : (marks b).space ⊆ K.space := by
    cases b
    · exact space_subset_of_le hAK
    · exact hCs.subset.trans (image_subset_iff.mpr hγK)
  obtain ⟨R, M, hR, hRK, hM⟩ :=
    K.exists_subdivision_with_finite_full_polyhedra hK marks hmarks hsub
  exact ⟨R, M false, M true, n, P, hR, hRK, (hM false).1, (hM false).2.1,
    (hM false).2.2, (hM true).1, (hM true).2.1.trans hCs, (hM true).2.2,
    hP, hPi, hPimage.trans ((hM true).2.1.trans hCs).symm⟩

end Geometry.SimplicialComplex
