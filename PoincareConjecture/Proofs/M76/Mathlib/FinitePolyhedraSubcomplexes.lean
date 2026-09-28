import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedronNeighborhoodRetraction

set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]

theorem exists_subdivision_with_finite_polyhedra
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : ι → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      ∀ i, L i ≤ R ∧ (L i).space = (J i).space := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  let (i : ι) : Fintype (J i).faces := (hJ i).fintype
  choose H hH using fun t : Σ i, (J i).faces =>
    t.2.val.exists_affine_halfspaces_convexHull ((J t.1).indep t.2.property)
  let Htotal := Finset.univ.biUnion H
  let n := hK.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ K.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hK.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨R, hR, hRK, _, hRH⟩ :=
    K.exists_subdivision_respectsAffineHyperplanes hK hn Htotal
  let L (i : ι) : SimplicialComplex ℝ E :=
    { faces := {s | s ∈ R.faces ∧ convexHull ℝ (s : Set E) ⊆ (J i).space}
      indep := fun hs => R.indep hs.1
      isRelLowerSet_faces := by
        intro s hs
        refine ⟨R.nonempty_of_mem_faces hs.1, ?_⟩
        intro t hts ht
        exact ⟨R.down_closed hs.1 hts ht, (convexHull_mono hts).trans hs.2⟩
      inter_subset_convexHull := fun hs ht => R.inter_subset_convexHull hs.1 ht.1 }
  refine ⟨R, L, hR, hRK, fun i => ⟨fun _ hs => hs.1, ?_⟩⟩
  ext x
  constructor
  · intro hx
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
    exact hs.2 hxs
  · intro hx
    have hxR : x ∈ R.space := hRK.space_eq.symm ▸ hJK i hx
    obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hx
    let j : Σ i, (J i).faces := ⟨i, t, ht⟩
    have hHi : ∀ A ∈ H j, R.RespectsAffineHyperplane A := fun A hA =>
      hRH A (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hA⟩)
    have hxH : ∀ A ∈ H j, A x ≤ 0 := by
      change x ∈ {y | ∀ A ∈ H j, A y ≤ 0}
      rw [← hH j]
      exact hxt
    obtain ⟨s, hs, hxs, hsH⟩ := R.exists_face_in_halfspaces (H j) hHi hxR hxH
    have hst : (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
      intro v hv
      rw [hH j]
      exact hsH v hv
    have hsJ : convexHull ℝ (s : Set E) ⊆ (J i).space :=
      (convexHull_min hst (convex_convexHull ℝ _)).trans ((J i).convexHull_subset_space ht)
    exact mem_space_iff.mpr ⟨s, ⟨hs, hsJ⟩, hxs⟩

theorem exists_subdivision_with_finite_full_polyhedra
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : ι → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      ∀ i, L i ≤ R ∧ (L i).space = (J i).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L i).vertices) → s ∈ (L i).faces := by
  classical
  obtain ⟨R, L, hR, hRK, hL⟩ :=
    K.exists_subdivision_with_finite_polyhedra hK J hJ hJK
  let : Fintype R.faces := hR.fintype
  let (i : ι) : Fintype (L i).faces := (hR.subset (hL i).1).fintype
  refine ⟨R.barycentricSubdivision, fun i => (L i).barycentricSubdivision,
    R.barycentricSubdivision_finite, R.barycentricSubdivision_isSubdivision.trans hRK,
    fun i => ⟨(L i).barycentricSubdivision_mono (hL i).1,
      (L i).barycentricSubdivision_isSubdivision.space_eq.trans (hL i).2, ?_⟩⟩
  exact fun s hs hv => R.barycentricSubdivision_full (hL i).1 hs hv

end Geometry.SimplicialComplex
