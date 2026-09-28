import PoincareConjecture.Proofs.M76.Mathlib.FineSimplicialSubdivision
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.HamiltonHandleCubeBall

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

theorem exists_finite_marked_face_cover
    {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    (K A : SimplicialComplex ℝ E) (hK : K.faces.Finite) (hA : A.faces.Finite)
    (hAK : A.space ⊆ K.space)
    (U : ι → Set K.space) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : K.space, ∃ i, x ∈ U i) :
    ∃ R B : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision K ∧ B.faces.Finite ∧ B ≤ R ∧
      B.space = A.space ∧
      (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ B.vertices) → s ∈ B.faces) ∧
      ∀ s ∈ R.faces, ∃ i, ∀ x : K.space,
        (x : E) ∈ convexHull ℝ (s : Set E) → x ∈ U i := by
  classical
  obtain ⟨L, hL, hLK, hstars⟩ := K.exists_finite_subdivision_stars hK U hU hcover
  have hAL : A.space ⊆ L.space := hAK.trans hLK.space_eq.symm.subset
  obtain ⟨R, B, hR, hRL, hB⟩ :=
    L.exists_subdivision_with_finite_full_polyhedra hL (fun _ : Unit => A)
      (fun _ => hA) (fun _ => hAL)
  refine ⟨R, B (), hR, hRL.trans hLK, hR.subset (hB ()).1,
    (hB ()).1, (hB ()).2.1, (hB ()).2.2, ?_⟩
  intro s hs
  obtain ⟨t, ht, hst⟩ := hRL.face_subset s hs
  obtain ⟨p, hpt⟩ := L.nonempty_of_mem_faces ht
  have hp : {p} ∈ L.faces :=
    L.down_closed ht (Finset.singleton_subset_iff.mpr hpt) (Finset.singleton_nonempty p)
  have hpt' : {p} ⊆ t := Finset.singleton_subset_iff.mpr hpt
  have htstar : t ∈ (L.closedFaceStar {p}).faces :=
    ⟨ht, by simpa only [Finset.union_eq_right.mpr hpt'] using ht⟩
  have hstar : convexHull ℝ (t : Set E) ⊆ (L.closedFaceStar {p}).space :=
    (L.closedFaceStar {p}).convexHull_subset_space htstar
  obtain ⟨i, hi⟩ := hstars p hp
  exact ⟨i, fun x hx => hi x (hstar (hst hx))⟩

local notation "V2" => (Fin 2 → ℝ)
local notation "D" => closedBall (0 : V2) 1
local notation "Q" => sphere (0 : V2) 1

theorem exists_marked_square_face_cover
    {ι : Type*} (U : ι → Set D) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ x : D, ∃ i, x ∈ U i) :
    ∃ K A : SimplicialComplex ℝ V2,
      K.faces.Finite ∧ K.space = D ∧ A.faces.Finite ∧ A ≤ K ∧ A.space = Q ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ A.vertices) → s ∈ A.faces) ∧
      ∀ s ∈ K.faces, ∃ i, ∀ x : D,
        (x : V2) ∈ convexHull ℝ (s : Set V2) → x ∈ U i := by
  obtain ⟨_, _, _, _, _, _, ⟨_, ⟨K₀, hK₀, hK₀s, _⟩, _⟩, _⟩ :=
    isFinitePLBallPair_unit_cube (ι := Fin 2)
  let A₀ := K₀.frontierSubcomplex D
  have hA₀ : A₀.faces.Finite := K₀.frontierSubcomplex_finite D hK₀
  have hA₀s : A₀.space = Q := by
    rw [K₀.frontierSubcomplex_space isClosed_closedBall (convex_closedBall _ _)
      ⟨0, ball_subset_interior_closedBall (mem_ball_self zero_lt_one)⟩ hK₀s,
      frontier_closedBall _ one_ne_zero]
  have hA₀K₀ : A₀.space ⊆ K₀.space := by
    rw [hA₀s, hK₀s]
    exact sphere_subset_closedBall
  let H : K₀.space ≃ₜ D := Homeomorph.setCongr hK₀s
  let V (i : ι) : Set K₀.space := H ⁻¹' U i
  have hV (i : ι) : IsOpen (V i) := (hU i).preimage H.continuous
  have hcoverV (x : K₀.space) : ∃ i, x ∈ V i := hcover (H x)
  obtain ⟨K, A, hK, hKK₀, hA, hAK, hAs, hfull, hfaces⟩ :=
    K₀.exists_finite_marked_face_cover A₀ hK₀ hA₀ hA₀K₀ V hV hcoverV
  refine ⟨K, A, hK, hKK₀.space_eq.trans hK₀s, hA, hAK, hAs.trans hA₀s,
    hfull, ?_⟩
  intro s hs
  obtain ⟨i, hi⟩ := hfaces s hs
  exact ⟨i, fun x hx => hi ⟨x, hK₀s.symm.subset x.property⟩ hx⟩

end Geometry.SimplicialComplex
