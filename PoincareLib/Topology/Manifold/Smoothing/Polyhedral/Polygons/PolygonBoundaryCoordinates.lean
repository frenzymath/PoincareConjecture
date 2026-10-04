import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.Polygons.PolygonBoundaryHomeomorph

/-!
# Exact edge coordinates for polygon boundary homeomorphisms

The simplicial boundary correspondence preserves each affine
edge parameter, and identifies the whole edge in both directions.
This is the diagonal matching needed for polygon disk gluing in
Erickson pp. 8--10. See M76 derivation 117.
-/

set_option autoImplicit false

open Set

namespace Polygon

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] {n : ℕ}

/-- A cyclic boundary homeomorphism can preserve the affine
parameter on every edge exactly. See M76 derivation 117. -/
theorem exists_boundary_homeomorph_edge_coordinates
    (P : Polygon E (n + 3)) (Q : Polygon F (n + 3))
    (hP : P.HasSimplicialEdges) (hQ : Q.HasSimplicialEdges)
    (hinjP : Function.Injective P) (hinjQ : Function.Injective Q) :
    ∃ e : P.boundary ℝ ≃ₜ Q.boundary ℝ,
      (∀ (i : Fin (n + 3)) (t : ℝ) (_ht : t ∈ Icc (0 : ℝ) 1)
        (hx : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t ∈ P.boundary ℝ),
        (e ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t, hx⟩ : F) =
          AffineMap.lineMap (Q i) (Q (finRotate (n + 3) i)) t) ∧
      (∀ (i : Fin (n + 3)) (x : P.boundary ℝ),
        (x : E) ∈ P.edgeSet ℝ i ↔ (e x : F) ∈ Q.edgeSet ℝ i) := by
  obtain ⟨f, _, H, hf, _, hfv, _, hH, _⟩ :=
    P.exists_simplicial_homeomorph Q hP hQ hinjP hinjQ
  let e := ((Homeomorph.setCongr (P.simplicialComplex_space hP).symm).trans H).trans
    (Homeomorph.setCongr (Q.simplicialComplex_space hQ))
  have he (x : P.boundary ℝ) : (e x : F) = f x := hH _
  have hparam (i : Fin (n + 3)) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1)
      (hx : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t ∈ P.boundary ℝ) :
      (e ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t, hx⟩ : F) =
        AffineMap.lineMap (Q i) (Q (finRotate (n + 3) i)) t := by
    obtain ⟨a, ha⟩ := hf _ (P.edgeVertices_mem_faces hP i)
    have hp : a (P i) = Q i :=
      (ha (subset_convexHull ℝ _ (by simp [edgeVertices]))).symm.trans (hfv i)
    have hq : a (P (finRotate (n + 3) i)) = Q (finRotate (n + 3) i) :=
      (ha (subset_convexHull ℝ _ (by simp [edgeVertices]))).symm.trans (hfv _)
    rw [he, ha, a.apply_lineMap, hp, hq]
    rw [← P.edgeSet_eq_convexHull]
    exact ⟨t, ht, rfl⟩
  refine ⟨e, hparam, ?_⟩
  intro i x
  constructor
  · rintro ⟨t, ht, heq⟩
    have hx : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t ∈ P.boundary ℝ :=
      heq.symm ▸ x.property
    have hsub : x = ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t, hx⟩ :=
      Subtype.ext heq.symm
    rw [hsub, hparam i t ht hx]
    exact ⟨t, ht, rfl⟩
  · rintro ⟨t, ht, heq⟩
    have hx : AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t ∈ P.boundary ℝ :=
      mem_iUnion.mpr ⟨i, t, ht, rfl⟩
    have hsub : e ⟨AffineMap.lineMap (P i) (P (finRotate (n + 3) i)) t, hx⟩ = e x :=
      Subtype.ext ((hparam i t ht hx).trans heq)
    have hv := congrArg (fun z : P.boundary ℝ => (z : E)) (e.injective hsub)
    exact ⟨t, ht, hv⟩

end Polygon
