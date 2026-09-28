import PoincareConjecture.Proofs.M76.PrimeReduction.RelativeChartStars











set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

variable {E F ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [Finite ι] [Finite κ]





theorem exists_full_subcomplex_faceAffine_marked_relative_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space)
    {S : Set E} (hS : IsClosed S)
    (N : ι → SimplicialComplex ℝ E) (hNK : ∀ i, (N i).space ⊆ K.space)
    (W : ι → Set K.space) (hW : ∀ i, IsOpen (W i))
    (hcover : ∀ x : K.space, (x : E) ∈ S → ∃ i, x ∈ W i)
    (hWN : ∀ i, Subtype.val '' W i ⊆ (N i).space)
    (f : ι → E → F) (hf : ∀ i, FinitePiecewiseAffineOn (f i) (N i).space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ t ∈ R.faces, (∀ v ∈ t, v ∈ (L a).vertices) → t ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, p ∈ S → ∃ i,
        (∀ x : K.space, (x : E) ∈ (R.closedStar p).space → x ∈ W i) ∧
        (R.closedStar p).space ⊆ (N i).space ∧
        (R.closedStar p).AffineOnFaces (f i) := by
  classical
  let N' : Option ι → SimplicialComplex ℝ E := fun i => i.elim K N
  let W' : Option ι → Set K.space := fun i =>
    i.elim (Subtype.val ⁻¹' Sᶜ) W
  let f' : Option ι → E → F := fun i => i.elim (fun _ => 0) f
  have hN' (i : Option ι) : (N' i).space ⊆ K.space := by
    cases i with
    | none => exact subset_rfl
    | some i => exact hNK i
  have hW' (i : Option ι) : IsOpen (W' i) := by
    cases i with
    | none => exact hS.isOpen_compl.preimage continuous_subtype_val
    | some i => exact hW i
  have hcover' (x : K.space) : ∃ i, x ∈ W' i := by
    by_cases hx : (x : E) ∈ S
    · obtain ⟨i, hi⟩ := hcover x hx
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩
  have hWN' (i : Option ι) : Subtype.val '' W' i ⊆ (N' i).space := by
    cases i with
    | none =>
        rintro _ ⟨x, _, rfl⟩
        exact x.property
    | some i => exact hWN i
  have hf' (i : Option ι) : FinitePiecewiseAffineOn (f' i) (N' i).space := by
    cases i with
    | none =>
        exact (K.affineOnFaces_affine
          (ContinuousAffineMap.const ℝ E (0 : F))).finitePiecewiseAffineOn hK
    | some i => exact hf i
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_relative_chart_stars hK J hJ hJK
      N' hN' W' hW' hcover' hWN' f' hf'
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp hpS
  have hpface : {p} ∈ R.faces := hp
  have hpstar : p ∈ (R.closedStar p).space := by
    apply (R.closedStar p).convexHull_subset_space (s := {p})
    · exact ⟨hpface, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
        using hpface⟩
    · simp
  have hpK : p ∈ K.space := hRK.space_eq.subset (R.vertices_subset_space hp)
  obtain ⟨i, hiW, hiN, hif⟩ := hstars p hp
  cases i with
  | none => exact False.elim ((hiW ⟨p, hpK⟩ hpstar) hpS)
  | some i => exact ⟨i, hiW, hiN, hif⟩

end Geometry.SimplicialComplex
