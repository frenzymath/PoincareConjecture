import PoincareLib.Topology.Manifold.Smoothing.Polyhedral.General.AlexanderComplexityOrdinary

/-!
# Actual disjoint polygon sections for Alexander recursion

Regular sections have complete finite disjoint polygon families,
with no isolated residue point. This property passes through
closed disjoint cuts and finite PL level comparisons, and it
implies zero charge. See Alexander 1924, pp. 6--8 and
M76 derivation 264.
-/

set_option autoImplicit false

open Set

namespace Set

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A regular section is exactly a finite disjoint union of
simple polygon boundaries. The empty family is allowed; an
isolated residue point is not. See Alexander p. 6 and derivation 264. -/
def HasDisjointPolygonPresentation (S : Set E) : Prop :=
  ∃ (m : ℕ) (n : Fin m → ℕ) (P : ∀ i, Polygon E (n i + 3)),
    (∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges) ∧
    S = ⋃ i, (P i).boundary ℝ ∧
    Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))

/-- Any finite disjoint polygon family supplies the canonical
regular presentation by reindexing. See Alexander p. 6 and
M76 derivation 264. -/
theorem hasDisjointPolygonPresentation_of_family {ι : Type*} [Finite ι]
    (n : ι → ℕ) (P : ∀ i, Polygon E (n i + 3))
    (hP : ∀ i, Function.Injective (P i) ∧ (P i).HasSimplicialEdges)
    {S : Set E} (hcover : S = ⋃ i, (P i).boundary ℝ)
    (hpair : Pairwise (fun i j => Disjoint ((P i).boundary ℝ) ((P j).boundary ℝ))) :
    HasDisjointPolygonPresentation S := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  refine ⟨Fintype.card ι, fun i => n (e i), fun i => P (e i),
    fun i => hP (e i), ?_, ?_⟩
  · change S = ⋃ i : Fin (Fintype.card ι), (P (e i)).boundary ℝ
    rw [e.surjective.iUnion_comp (fun i => (P i).boundary ℝ)]
    exact hcover
  · intro i j hij
    exact hpair (fun h => hij (e.injective h))

/-- Actual regular polygon sections have zero Alexander
charge with the empty residue. See Alexander p. 6 and
M76 derivation 264. -/
theorem HasDisjointPolygonPresentation.hasAlexanderCurvePresentation
    {S : Set E} (h : HasDisjointPolygonPresentation S) :
    HasAlexanderCurvePresentation S 0 := by
  obtain ⟨m, n, P, hP, hcover, hpair⟩ := h
  exact hasAlexanderCurvePresentation_zero_of_disjoint_family n P hP hpair
    (r := ∅) subsingleton_empty (by simpa only [empty_union] using hcover)

variable [FiniteDimensional ℝ E]

/-- A finite PL comparison preserves the complete regular
polygon presentation. See Alexander pp. 6--8 and derivation 264. -/
theorem HasDisjointPolygonPresentation.of_finitePL
    {S : Set E} {T : Set F} (h : HasDisjointPolygonPresentation S)
    (e : S ≃ₜ T) (he : e.IsFinitePL) : HasDisjointPolygonPresentation T := by
  obtain ⟨m, n, P, hP, hcover, hpair⟩ := h
  obtain ⟨N, Q, hQ, htarget, hQpair⟩ := Polygon.exists_disjoint_finitePL_image_family
    n P (fun i => (hP i).2) (fun i => (hP i).1) hpair hcover e he
  exact ⟨m, N, Q, hQ, htarget, hQpair⟩

/-- A closed disjoint partition of a regular section retains
whole polygons on both sides. See Alexander pp. 6--8 and
M76 derivation 264. -/
theorem HasDisjointPolygonPresentation.closed_cut
    {S T : Set E} (h : HasDisjointPolygonPresentation (S ∪ T))
    (hS : IsClosed S) (hT : IsClosed T) (hsep : Disjoint S T) :
    HasDisjointPolygonPresentation S ∧ HasDisjointPolygonPresentation T := by
  obtain ⟨m, n, P, hP, hcover, hpair⟩ := h
  obtain ⟨I, hI, hIc, hpI, hpIc⟩ := Polygon.exists_disjoint_polygon_family_of_closed_cut
    n P (fun i => (hP i).2) (fun i => (hP i).1) hpair hS hT hsep hcover
  exact ⟨hasDisjointPolygonPresentation_of_family (fun i : I => n i)
      (fun i => P i) (fun i => hP i) hI hpI,
    hasDisjointPolygonPresentation_of_family (fun i : (Iᶜ : Set (Fin m)) => n i)
      (fun i => P i) (fun i => hP i) hIc hpIc⟩

/-- Removing a closed separate part and transporting the
remainder preserves its actual regular polygon union. No
separate closedness hypothesis on the remainder is needed.
See Alexander p. 7 and M76 derivation 264. -/
theorem HasDisjointPolygonPresentation.finitePL_remainder
    {b X : Set E} {Y : Set F} (h : HasDisjointPolygonPresentation (b ∪ X))
    (hb : IsClosed b) (hsep : Disjoint b X) (e : X ≃ₜ Y) (he : e.IsFinitePL) :
    HasDisjointPolygonPresentation Y := by
  obtain ⟨m, n, P, hP, hcover, hpair⟩ := h
  obtain ⟨I, N, Q, hQ, htarget, hQpair⟩ :=
    Polygon.exists_disjoint_finitePL_remainder_family n P
      (fun i => (hP i).2) (fun i => (hP i).1) hpair hb hsep hcover e he
  exact hasDisjointPolygonPresentation_of_family N Q hQ htarget hQpair

end Set
