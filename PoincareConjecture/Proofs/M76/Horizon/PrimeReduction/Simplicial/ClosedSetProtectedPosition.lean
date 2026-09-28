import PoincareConjecture.Proofs.M76.Dehn.Mathlib.ProtectedFinitePolyhedronPosition
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralRefinement
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralIntersections
import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedralUnions
import PoincareConjecture.Proofs.M76.Horizon.PrimeReduction.General.FiniteVertexSignBudget

set_option autoImplicit false

open Set unitInterval Topology

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

omit [FiniteDimensional ℝ E] in
private theorem closed_protection_avoids_free_closure
    (P P₀ : SimplicialComplex ℝ E) (hP : P.faces.Finite)
    {Z : Set E}
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x) :
    Z ⊆ (closure (P.space \ P₀.space))ᶜ := by
  intro x hxZ hxcl
  have hxP : x ∈ P.space :=
    (closure_minimal sdiff_subset (P.isCompact_space_of_finite hP).isClosed) hxcl
  obtain ⟨N, hNP₀, hN, hxN⟩ := mem_nhds_iff.mp (hnear ⟨x, hxP⟩ hxZ)
  obtain ⟨U, hU, hUN⟩ := isOpen_induced_iff.mp hN
  have hxU : x ∈ U := (Set.ext_iff.mp hUN ⟨x, hxP⟩).mpr hxN
  obtain ⟨y, hyU, hyP, hyP₀⟩ := mem_closure_iff.mp hxcl U hU hxU
  exact hyP₀ (hNP₀ ((Set.ext_iff.mp hUN ⟨y, hyP⟩).mp hyU))

theorem exists_ambient_protection_of_relative_neighborhood
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    {Z : Set E} (hZ : IsClosed Z)
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x) :
    ∃ Q : SimplicialComplex ℝ E, Q.faces.Finite ∧ Q.space ⊆ J.space ∧
      P₀.space ⊆ Q.space ∧ frontier J.space ⊆ Q.space ∧
      P.space ∩ Q.space ⊆ P₀.space ∧
      ∃ U : Set E, IsOpen U ∧ Z ⊆ U ∧ U ∩ J.space ⊆ Q.space := by
  have havoid := closed_protection_avoids_free_closure P P₀ hP hnear
  obtain ⟨B, hB, hBin, hBout⟩ := exists_finite_neighborhood_subset_normed
    ((J.isCompact_space_of_finite hJ).inter_right hZ)
    (isClosed_closure.isOpen_compl) (fun _ hx => havoid hx.2)
  obtain ⟨N, hN, hNs⟩ := B.exists_finite_triangulation_inter J hB hJ
  obtain ⟨F, hF, hFs⟩ := J.exists_finite_convex_frontier_triangulation hJ hcv
  obtain ⟨D, hD, hDs⟩ := P₀.exists_finite_triangulation_union N hP₀ hN
  obtain ⟨Q, hQ, hQs⟩ := D.exists_finite_triangulation_union F hD hF
  have hQspace : Q.space = (P₀.space ∪ (B.space ∩ J.space)) ∪ frontier J.space := by
    rw [hQs, hDs, hNs, hFs]
  refine ⟨Q, hQ, ?_, ?_, ?_, ?_, interior B.space ∪ J.spaceᶜ,
    isOpen_interior.union (J.isCompact_space_of_finite hJ).isClosed.isOpen_compl, ?_, ?_⟩
  · rw [hQspace]
    exact union_subset (union_subset (hP₀P.trans hPJ) inter_subset_right)
      (J.isCompact_space_of_finite hJ).isClosed.frontier_subset
  · rw [hQspace]
    exact subset_union_left.trans subset_union_left
  · rw [hQspace]
    exact subset_union_right
  · rintro x ⟨hxP, hxQ⟩
    rw [hQspace] at hxQ
    rcases hxQ with (hxP₀ | hxB) | hxf
    · exact hxP₀
    · by_contra hxP₀
      exact hBout hxB.1 (subset_closure ⟨hxP, hxP₀⟩)
    · exact hfront ⟨hxP, hxf⟩
  · intro x hxZ
    by_cases hxJ : x ∈ J.space
    · exact Or.inl (hBin ⟨hxJ, hxZ⟩)
    · exact Or.inr hxJ
  · rintro x ⟨hxU, hxJ⟩
    rw [hQspace]
    rcases hxU with hxB | hxJ'
    · exact Or.inl (Or.inr ⟨interior_subset hxB, hxJ⟩)
    · exact False.elim (hxJ' hxJ)

theorem exists_closed_set_protected_finite_polyhedron_position_with_height
    {ι : Type*} [Finite ι]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    {Z : Set E} (hZ : IsClosed Z)
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x)
    (L : ι → SimplicialComplex ℝ E) (hL : ∀ i, (L i).faces.Finite)
    (A : E →ᵃ[ℝ] ℝ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R K K₀ : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      ∃ H : PLCarrierMotion J.space P₀.space ε,
        R.AffineOnFaces (H.map 1) ∧
        (∃ A : SimplicialComplex ℝ E,
          A.faces.Finite ∧ A.space = H.map 1 '' P.space) ∧
        (∀ τ, EqOn (H.map τ) id Z) ∧
        (∃ U : Set E, IsOpen U ∧ Z ⊆ U ∧ ∀ τ, EqOn (H.map τ) id U) ∧
        (∀ τ v, v ∈ R.vertices →
          (A v < 0 → A (H.map τ v) < 0) ∧ (0 < A v → 0 < A (H.map τ v))) ∧
        ∀ i s, s ∈ K.faces → s ∉ K₀.faces → ∀ t, t ∈ (L i).faces →
          affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
              (convexHull ℝ (t : Set E)) := by
  classical
  obtain ⟨B, hB, hBJ, hP₀B, hfrontB, hPB, U, hU, hZU, hUJ⟩ :=
    J.exists_ambient_protection_of_relative_neighborhood P P₀ hJ hP hP₀
      hcv hP₀P hPJ hfront hZ hnear
  let M : Option Bool → SimplicialComplex ℝ E
    | none => B
    | some false => P₀
    | some true => P
  have hM : ∀ i, (M i).faces.Finite := by
    intro i
    cases i with
    | none => exact hB
    | some b => cases b <;> assumption
  have hMJ : ∀ i, (M i).space ⊆ J.space := by
    intro i
    cases i with
    | none => exact hBJ
    | some b =>
      cases b
      · exact hP₀P.trans hPJ
      · exact hPJ
  obtain ⟨R, T, hR, hRJ, hT⟩ :=
    J.exists_subdivision_with_finite_full_polyhedra hJ M hM hMJ
  let K := T (some true)
  let K₀ := T (some false)
  let Q := T none
  have hK : K ≤ R := (hT (some true)).1
  have hK₀ : K₀ ≤ R := (hT (some false)).1
  have hQ : Q ≤ R := (hT none).1
  have hKs : K.space = P.space := (hT (some true)).2.1
  have hK₀s : K₀.space = P₀.space := (hT (some false)).2.1
  have hQs : Q.space = B.space := (hT none).2.1
  have hK₀K : K₀ ≤ K := by
    intro s hs
    apply (hT (some true)).2.2 s (hK₀ hs)
    intro v hv
    apply mem_subcomplex_vertices_of_mem_space hK
    · exact R.down_closed (hK₀ hs) (Finset.singleton_subset_iff.mpr hv)
        (Finset.singleton_nonempty v)
    · rw [hKs]
      exact hP₀P (hK₀s ▸ K₀.subset_space hs hv)
  have hfull : ∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces :=
    fun s hs => (hT (some false)).2.2 s (hK hs)
  have hfree : ∀ v ∈ K.vertices, v ∉ K₀.vertices → v ∉ Q.vertices := by
    intro v hv hv₀ hvQ
    apply hv₀
    apply mem_subcomplex_vertices_of_mem_space hK₀ (hK hv)
    rw [hK₀s]
    exact hPB ⟨hKs ▸ K.vertices_subset_space hv, hQs ▸ Q.vertices_subset_space hvQ⟩
  have hRs : R.space = J.space := hRJ.space_eq
  have hRcv : Convex ℝ R.space := hRs.symm ▸ hcv
  have hRQfront : frontier R.space ⊆ Q.space := by
    rw [hRs, hQs]
    exact hfrontB
  have hK₀Q : K₀.space ⊆ Q.space := by
    rw [hK₀s, hQs]
    exact hP₀B
  obtain ⟨δ, hδ, hsign⟩ :=
    (R.finite_vertices_of_finite_faces hR).exists_strict_sign_preserving_radius
      A.continuous_of_finiteDimensional
  obtain ⟨H, hHaff, hHfixed, hHfaces⟩ :=
    exists_protected_finite_complex_position R Q K K₀ hR hRcv hQ hRQfront hK
      hfull hK₀Q hfree L hL (lt_min hε hδ)
  let F : PLCarrierMotion J.space P₀.space ε :=
    { map := H.map
      continuous_map := H.continuous_map
      continuous_symm := H.continuous_symm
      zero := H.zero
      outside := by simpa only [hRs] using H.outside
      fixed_protected := fun τ x hx => hHfixed τ x (hK₀s.symm ▸ hx)
      carrier := by simpa only [hRs] using H.carrier
      finitePL := by
        rw [← hRs]
        exact H.finitePL
      small := fun τ x => (H.small τ x).trans_le (min_le_left _ _) }
  have hFU : ∀ τ, EqOn (F.map τ) id U := by
    intro τ x hxU
    by_cases hxJ : x ∈ J.space
    · exact H.fixed_protected τ x (hQs.symm ▸ hUJ ⟨hxU, hxJ⟩)
    · exact F.outside τ x (fun hx => hxJ (interior_subset hx))
  refine ⟨R, K, K₀, hR, hRJ, hK, hKs, hK₀K, hK₀s, hfull,
    F, hHaff, ?_, fun τ => (hFU τ).mono hZU, ⟨U, hU, hZU, hFU⟩, ?_, hHfaces⟩
  · have hKaff : K.AffineOnFaces (H.map 1) := fun s hs => hHaff s (hK hs)
    have hinj : InjOn (H.map 1) K.space := (H.map 1).injective.injOn
    refine ⟨hKaff.embeddedImage hinj, hKaff.embeddedImage_finite hinj (hR.subset hK), ?_⟩
    rw [hKaff.embeddedImage_space hinj, hKs]
  · intro τ v hv
    exact hsign v hv (H.map τ v) ((H.small τ v).trans_le (min_le_right _ _))

theorem exists_closed_set_protected_finite_polyhedron_position
    {ι : Type*} [Finite ι]
    (J P P₀ : SimplicialComplex ℝ E)
    (hJ : J.faces.Finite) (hP : P.faces.Finite) (hP₀ : P₀.faces.Finite)
    (hcv : Convex ℝ J.space) (hP₀P : P₀.space ⊆ P.space)
    (hPJ : P.space ⊆ J.space)
    (hfront : P.space ∩ frontier J.space ⊆ P₀.space)
    {Z : Set E} (hZ : IsClosed Z)
    (hnear : ∀ x : P.space, (x : E) ∈ Z →
      (Subtype.val ⁻¹' P₀.space : Set P.space) ∈ 𝓝 x)
    (L : ι → SimplicialComplex ℝ E) (hL : ∀ i, (L i).faces.Finite)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R K K₀ : SimplicialComplex ℝ E,
      R.faces.Finite ∧ R.IsSubdivision J ∧ K ≤ R ∧ K.space = P.space ∧
      K₀ ≤ K ∧ K₀.space = P₀.space ∧
      (∀ s ∈ K.faces, (∀ v ∈ s, v ∈ K₀.vertices) → s ∈ K₀.faces) ∧
      ∃ H : PLCarrierMotion J.space P₀.space ε,
        R.AffineOnFaces (H.map 1) ∧
        (∃ A : SimplicialComplex ℝ E,
          A.faces.Finite ∧ A.space = H.map 1 '' P.space) ∧
        (∀ τ, EqOn (H.map τ) id Z) ∧
        (∃ U : Set E, IsOpen U ∧ Z ⊆ U ∧ ∀ τ, EqOn (H.map τ) id U) ∧
        ∀ i s, s ∈ K.faces → s ∉ K₀.faces → ∀ t, t ∈ (L i).faces →
          affineSpan ℝ (H.map 1 '' (s : Set E) ∪ (t : Set E)) = ⊤ ∨
            Disjoint (intrinsicInterior ℝ (convexHull ℝ (H.map 1 '' (s : Set E))))
              (convexHull ℝ (t : Set E)) := by
  obtain ⟨R, K, K₀, hR, hRJ, hKR, hKs, hK₀K, hK₀s, hfull,
      H, hH, hA, hHZ, hHU, _, hpos⟩ :=
    J.exists_closed_set_protected_finite_polyhedron_position_with_height P P₀ hJ hP hP₀
      hcv hP₀P hPJ hfront hZ hnear L hL 0 hε
  exact ⟨R, K, K₀, hR, hRJ, hKR, hKs, hK₀K, hK₀s, hfull,
    H, hH, hA, hHZ, hHU, hpos⟩

end Geometry.SimplicialComplex
