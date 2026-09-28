import PoincareConjecture.Proofs.M76.Mathlib.TranslatedOriginalEventBody
import PoincareConjecture.Proofs.M76.Mathlib.PolygonSliceCoordinates











set_option autoImplicit false

open Set Geometry

namespace Polygon

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E] {n : ℕ}






theorem exists_original_vertex_event_bodies
    {ι : Type*} [Finite ι] [Nonempty ι]
    (P : Polygon E n) (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (hpure : ∀ s ∈ K.faces, ∃ t ∈ K.faces, t.card = 3 ∧ s ⊆ t)
    (hcofaces : ∀ s ∈ K.faces, s.card = 2 →
      {t : Finset E | t ∈ K.faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2)
    (hlinks : ∀ p ∈ K.vertices, IsConnected (K.link p).space)
    (hPK : P.boundary ℝ ⊆ K.space)
    (U : Fin n → Set E) (hU : ∀ i, IsOpen (U i)) (hPU : ∀ i, P i ∈ U i)
    (c : E ≃L[ℝ] (ι → ℝ)) :
    let e := fun i => ContinuousAffineEquiv.constVAdd ℝ E (-P i)
    let K0 := fun i =>
      (K.affineOnFaces_affine (e i).toContinuousAffineMap).embeddedImage (e i).injective.injOn
    ∃ (M : Fin n → SimplicialComplex ℝ E) (C : Fin n → Set E)
      (L : Fin n → (ι ⊕ ι) → E →ₗ[ℝ] ℝ) (J : Fin n → SimplicialComplex ℝ E),
      ∀ i, (K0 i).faces.Finite ∧ (K0 i).space = e i '' K.space ∧
      (∀ s ∈ (K0 i).faces, s.card ≤ 3) ∧
      (M i).faces.Finite ∧ (M i).space = (K0 i).space ∧ (0 : E) ∈ (M i).vertices ∧
      (∀ s ∈ (M i).faces, ∃ t ∈ (M i).faces, t.card = 3 ∧ s ⊆ t) ∧
      (∀ s ∈ (M i).faces, s.card = 2 →
        {t : Finset E | t ∈ (M i).faces ∧ t.card = 3 ∧ s ⊆ t}.ncard = 2) ∧
      ((M i).link 0).vertexAbstractComplex.edgeGraph.Connected ∧
      IsCompact (C i) ∧ Convex ℝ (C i) ∧ (0 : E) ∈ interior (C i) ∧ C i ⊆ e i '' U i ∧
      Disjoint (C i) ((M i).link 0).space ∧
      (M i).space ∩ C i = ((M i).closedStar 0).space ∩ C i ∧
      (∀ s ∈ (K0 i).faces, (convexHull ℝ (s : Set E) ∩ C i).Nonempty →
        (0 : E) ∈ convexHull ℝ (s : Set E)) ∧
      (∀ j, L i j ≠ 0) ∧ C i = {x | ∀ j, L i j x ≤ 1} ∧
      (J i).faces.Finite ∧ (J i).space = frontier (C i) ∧
      IsCompact ((e i).symm '' C i) ∧ Convex ℝ ((e i).symm '' C i) ∧
      P i ∈ interior ((e i).symm '' C i) ∧ (e i).symm '' C i ⊆ U i ∧
      ∀ s ∈ K.faces, (convexHull ℝ (s : Set E) ∩ ((e i).symm '' C i)).Nonempty →
        P i ∈ convexHull ℝ (s : Set E) := by
  have hbody (i : Fin n) := K.exists_original_event_body_in_centered_coordinates
    hK hpure hcofaces hlinks (hPK (P.vertex_mem_boundary i))
    (ContinuousAffineEquiv.constVAdd ℝ E (-P i))
    (by change -P i + P i = 0; exact neg_add_cancel (P i)) (hU i) (hPU i) c
  choose M C L J hgeom using hbody
  exact ⟨M, C, L, J, hgeom⟩

end Polygon
