import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Terminal.RimRefinement
import PoincareConjecture.Proofs.M76.Horizon.Polyhedral.Simplicial.RefinementEdgeStars
import PoincareConjecture.Proofs.M76.Mathlib.SimplicialCompatibleUnion
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLBallImages
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLSubsets

set_option autoImplicit false
open Set Metric Geometry
open PoincareConjecture.M76.Dehn

namespace Geometry.SimplicialComplex

local notation "V2" => (Fin 2 → ℝ)
local notation "Q2" => sphere (0 : V2) 1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem exists_refinement_with_paired_embedded_rims
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hAK : A ≤ K)
    (γ : Bool → V2 → E) (hγ : ∀ b, FinitePiecewiseAffineOn (γ b) Q2)
    (hinj : ∀ b, InjOn (γ b) Q2) (hγA : ∀ b, MapsTo (γ b) Q2 A.space)
    (hdis : Disjoint (γ false '' Q2) (γ true '' Q2)) :
    ∃ (R B U : SimplicialComplex ℝ E) (L : Bool → SimplicialComplex ℝ E)
      (n : Bool → ℕ) (P : ∀ b, Polygon E (n b + 3))
      (Γ : ∀ b, Q2 ≃ₜ (L b).space),
      R.faces.Finite ∧ R.IsSubdivision K ∧ B ≤ R ∧ B.space = A.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ B.vertices) → s ∈ B.faces) ∧
      U ≤ B ∧ U.faces = (L false).faces ∪ (L true).faces ∧
      U.space = (γ false '' Q2) ∪ (γ true '' Q2) ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ U.vertices) → s ∈ U.faces) ∧
      Disjoint (L false).space (L true).space ∧
      ∀ b, L b ≤ U ∧ L b ≤ B ∧ (L b).space = γ b '' Q2 ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L b).vertices) → s ∈ (L b).faces) ∧
        (P b).HasSimplicialEdges ∧ Function.Injective (P b) ∧
        (P b).boundary ℝ = (L b).space ∧ (Γ b).IsFinitePL ∧
        (Γ b).symm.IsFinitePL ∧ ∀ u : Q2, (Γ b u : E) = γ b u := by
  classical
  have hpolygons (b : Bool) : ∃ (n : ℕ) (P : Polygon E (n + 3)),
      P.HasSimplicialEdges ∧ Function.Injective P ∧ P.boundary ℝ = γ b '' Q2 := by
    obtain ⟨n, P, hPi, hP, hPs⟩ := squareRimPolygon.exists_polygon_finitePL_image
      hasSimplicialEdges_squareRimPolygon injective_squareRimPolygon (hγ b)
      boundary_squareRimPolygon.subset (boundary_squareRimPolygon.symm ▸ hinj b)
    exact ⟨n, P, hP, hPi, by rwa [boundary_squareRimPolygon] at hPs⟩
  choose n P hP hPi hPimage using hpolygons
  let C (b : Bool) := (P b).simplicialComplex (hP b)
  have hC (b : Bool) : (C b).faces.Finite :=
    (P b).finite_simplicialComplex_faces (hP b)
  have hCs (b : Bool) : (C b).space = γ b '' Q2 :=
    ((P b).simplicialComplex_space (hP b)).trans (hPimage b)
  have hγimage (b : Bool) : γ b '' Q2 ⊆ A.space := by
    rintro _ ⟨x, hx, rfl⟩
    exact hγA b hx
  have hcross : ∀ s ∈ (C false).faces, ∀ t ∈ (C true).faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) := by
    intro s hs t ht x hx
    exact False.elim (Set.disjoint_left.mp hdis
      (hCs false ▸ (C false).convexHull_subset_space hs hx.1)
      (hCs true ▸ (C true).convexHull_subset_space ht hx.2))
  let CU := (C false).unionOfCompatible (C true) hcross
  have hCU : CU.faces.Finite :=
    finite_faces_unionOfCompatible _ _ hcross (hC false) (hC true)
  have hCUs : CU.space = (γ false '' Q2) ∪ (γ true '' Q2) := by
    rw [space_unionOfCompatible, hCs, hCs]
  let marks : Bool ⊕ Bool → SimplicialComplex ℝ E
    | .inl false => A
    | .inl true => CU
    | .inr b => C b
  have hmarks : ∀ i, (marks i).faces.Finite := by
    rintro (b | b)
    · cases b
      · exact hK.subset hAK
      · exact hCU
    · exact hC b
  have hsub : ∀ i, (marks i).space ⊆ K.space := by
    rintro (b | b)
    · cases b
      · exact space_subset_of_le hAK
      · change CU.space ⊆ K.space
        rw [hCUs]
        exact union_subset
          ((hγimage false).trans (space_subset_of_le hAK))
          ((hγimage true).trans (space_subset_of_le hAK))
    · change (C b).space ⊆ K.space
      rw [hCs]
      exact (hγimage b).trans (space_subset_of_le hAK)
  obtain ⟨R, M, hR, hRK, hM⟩ :=
    K.exists_subdivision_with_finite_full_polyhedra hK marks hmarks hsub
  let B := M (.inl false)
  let U := M (.inl true)
  let L (b : Bool) := M (.inr b)
  have hBR : B ≤ R := (hM (.inl false)).1
  have hUR : U ≤ R := (hM (.inl true)).1
  have hLR (b : Bool) : L b ≤ R := (hM (.inr b)).1
  have hBs : B.space = A.space := (hM (.inl false)).2.1
  have hUs : U.space = (γ false '' Q2) ∪ (γ true '' Q2) :=
    (hM (.inl true)).2.1.trans hCUs
  have hLs (b : Bool) : (L b).space = γ b '' Q2 :=
    (hM (.inr b)).2.1.trans (hCs b)
  have hUB : U ≤ B := R.le_of_common_subcomplex_space_subset U B hUR hBR (by
    rw [hUs, hBs]
    exact union_subset (hγimage false) (hγimage true))
  have hLU (b : Bool) : L b ≤ U :=
    R.le_of_common_subcomplex_space_subset (L b) U (hLR b) hUR (by
      rw [hLs, hUs]
      cases b
      · exact subset_union_left
      · exact subset_union_right)
  have hLcross : ∀ s ∈ (L false).faces, ∀ t ∈ (L true).faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ t) :=
    fun _ hs _ ht ↦ R.inter_subset_convexHull (hLR false hs) (hLR true ht)
  let LU := (L false).unionOfCompatible (L true) hLcross
  have hLUR : LU ≤ R := fun _ hs ↦ hs.elim (fun hs ↦ hLR false hs)
    (fun hs ↦ hLR true hs)
  have hLUs : LU.space = U.space := by
    rw [space_unionOfCompatible, hLs, hLs, hUs]
  have hLUeq : LU = U := le_antisymm
    (R.le_of_common_subcomplex_space_subset LU U hLUR hUR hLUs.subset)
    (R.le_of_common_subcomplex_space_subset U LU hUR hLUR hLUs.symm.subset)
  have hUfaces : U.faces = (L false).faces ∪ (L true).faces := by
    rw [← hLUeq]
    rfl
  have hΓ (b : Bool) : ∃ Γ : Q2 ≃ₜ (L b).space,
      Γ.IsFinitePL ∧ Γ.symm.IsFinitePL ∧ ∀ u : Q2, (Γ u : E) = γ b u := by
    obtain ⟨Γ, hΓ, hΓv⟩ := (hγ b).exists_homeomorph_image (hinj b)
    let Γ' := Γ.trans (Homeomorph.setCongr (hLs b).symm)
    have hΓ' : Γ'.IsFinitePL := hΓ.setCongr rfl (hLs b).symm
    exact ⟨Γ', hΓ', hΓ'.symm, hΓv⟩
  choose Γ hΓPL hΓinv hΓv using hΓ
  refine ⟨R, B, U, L, n, P, Γ, hR, hRK, hBR, hBs, (hM (.inl false)).2.2,
    hUB, hUfaces, hUs, (hM (.inl true)).2.2, ?_, ?_⟩
  · rwa [hLs, hLs]
  · intro b
    exact ⟨hLU b, (hLU b).trans hUB, hLs b, (hM (.inr b)).2.2, hP b, hPi b,
      (hPimage b).trans (hLs b).symm, hΓPL b, hΓinv b, hΓv b⟩

end Geometry.SimplicialComplex
