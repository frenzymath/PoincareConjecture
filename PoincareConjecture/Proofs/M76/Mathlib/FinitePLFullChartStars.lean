import PoincareConjecture.Proofs.M76.Mathlib.FinitePolyhedraSubcomplexes
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLProduct
import PoincareConjecture.Proofs.M76.Mathlib.SupportedFinitePLExtension
import PoincareConjecture.Proofs.M76.Mathlib.LocallyPiecewiseAffine










set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι κ : Type*} [Finite ι] [Finite κ]






theorem exists_full_subcomplex_faceAffine_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space)
    {C : Set E} (hC : IsClosed C)
    (N : ι → SimplicialComplex ℝ E) (hN : ∀ i, (N i).faces.Finite)
    (hNK : ∀ i, (N i).space ⊆ K.space)
    (f : ι → E → F) (hf : ∀ i, (N i).AffineOnFaces (f i))
    (hcover : ∀ x ∈ C, ∃ i, x ∈ interior (N i).space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, L i ≤ R ∧ (L i).space = (J i).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L i).vertices) → s ∈ (L i).faces) ∧
      ∀ p ∈ R.vertices, p ∈ C → ∃ i,
        (R.closedStar p).space ⊆ interior (N i).space ∧
        (R.closedStar p).AffineOnFaces (f i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose g hg hgf _ _ using fun i =>
    ((hf i).finitePiecewiseAffineOn (hN i)).exists_supported_extension
      K hK (hNK i) isOpen_univ (subset_univ _)
  obtain ⟨T, hT, hTK, hgT⟩ := FinitePiecewiseAffineOn.pi_on_complex K hK hg
  obtain ⟨S, hS, hSK, hST⟩ := K.exists_common_finite_subdivision T hK hT hTK.symm
  have hgS (i : ι) : S.AffineOnFaces (g i) :=
    (hST.affineOnFaces hgT).postcomp
      (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).toContinuousAffineMap
  let U : Option ι → Set K.space := fun i => match i with
    | none => Subtype.val ⁻¹' Cᶜ
    | some j => Subtype.val ⁻¹' interior (N j).space
  have hU (i : Option ι) : IsOpen (U i) := by
    cases i with
    | none => exact hC.isOpen_compl.preimage continuous_subtype_val
    | some i => exact isOpen_interior.preimage continuous_subtype_val
  have hUC (x : K.space) : ∃ i, x ∈ U i := by
    by_cases hx : (x : E) ∈ C
    · obtain ⟨i, hi⟩ := hcover x hx
      exact ⟨some i, hi⟩
    · exact ⟨none, hx⟩
  obtain ⟨delta, hdelta, hstars⟩ := K.exists_mesh_for_subdivision_stars hK U hU hUC
  let n := hS.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ S.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hS.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨A, hA, hAS, _, hdiam⟩ := S.exists_finite_subdivision_mesh hS hn hdelta
  have hAK := hAS.trans hSK
  obtain ⟨R, L, hR, hRA, hL⟩ := A.exists_subdivision_with_finite_full_polyhedra hA J hJ
    (fun i x hx => hAK.space_eq.symm.subset (hJK i hx))
  have hRK := hRA.trans hAK
  have hRdiam (s : Finset E) (hs : s ∈ R.faces) :
      diam (convexHull ℝ (s : Set E)) ≤ delta := by
    obtain ⟨t, ht, hst⟩ := hRA.face_subset s hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans
      (hdiam t ht)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp hpC
  have hpface : {p} ∈ R.faces := hp
  have hstar : R.closedFaceStar {p} = R.closedStar p := by
    ext s
    simp only [closedFaceStar, closedStar, Finset.singleton_union]
  have hpstar : p ∈ (R.closedStar p).space := by
    apply (R.closedStar p).convexHull_subset_space (s := {p})
    · exact ⟨hpface, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
        using hpface⟩
    · simp
  have hpK : p ∈ K.space := hRK.space_eq.subset (R.vertices_subset_space hp)
  obtain ⟨i, hi⟩ := hstars R hRK hRdiam p hpface
  cases i with
  | none =>
      exact False.elim ((hi ⟨p, hpK⟩ (hstar.symm ▸ hpstar)) hpC)
  | some i =>
      have hsub : (R.closedStar p).space ⊆ interior (N i).space := by
        intro x hx
        have hxR : x ∈ R.space := by
          obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
          exact R.convexHull_subset_space hs.1 hxs
        exact hi ⟨x, hRK.space_eq.subset hxR⟩ (hstar.symm ▸ hx)
      have hgR : R.AffineOnFaces (g i) := (hRA.trans hAS).affineOnFaces (hgS i)
      refine ⟨i, hsub, ?_⟩
      exact (show (R.closedStar p).AffineOnFaces (g i) from
        fun s hs => hgR s hs.1).congr
          (fun x hx => hgf i (interior_subset (hsub hx)))





theorem exists_full_subcomplex_faceAffine_local_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space)
    {C : Set E} (hC : IsCompact C) (hCK : C ⊆ interior K.space)
    (f : C → E → F) (U : C → Set E)
    (hf : ∀ x, LocallyPiecewiseAffineOn (f x) (U x))
    (hpoint : ∀ x : C, (x : E) ∈ U x) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, L i ≤ R ∧ (L i).space = (J i).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L i).vertices) → s ∈ (L i).faces) ∧
      ∀ p ∈ R.vertices, p ∈ C → ∃ x : C,
        (R.closedStar p).space ⊆ U x ∧
        (R.closedStar p).AffineOnFaces (f x) := by
  classical
  have hlocal (x : C) : ∃ N : SimplicialComplex ℝ E,
      N.faces.Finite ∧ (x : E) ∈ interior N.space ∧
      N.space ⊆ U x ∩ interior K.space ∧ N.AffineOnFaces (f x) := by
    exact ((hf x).mono ((hf x).isOpen.inter isOpen_interior) inter_subset_left)
      x ⟨hpoint x, hCK x.property⟩
  choose N hN hxN hNU hfN using hlocal
  let : CompactSpace C := isCompact_iff_compactSpace.mp hC
  let V : C → Set C := fun x => Subtype.val ⁻¹' interior (N x).space
  have hV (x : C) : IsOpen (V x) := isOpen_interior.preimage continuous_subtype_val
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover V hV
    (fun x _ => mem_iUnion.mpr ⟨x, hxN x⟩)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_chart_stars hK J hJ hJK hC.isClosed
      (fun x : t => N x) (fun x => hN x)
      (fun x y hy => interior_subset (hNU x hy).2)
      (fun x : t => f x) (fun x => hfN x) (by
        intro x hx
        obtain ⟨y, hyt, hy⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨x, hx⟩ : C)))
        exact ⟨⟨y, hyt⟩, hy⟩)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp hpC
  obtain ⟨x, hsub, hface⟩ := hstars p hp hpC
  exact ⟨x, fun y hy => (hNU x (interior_subset (hsub hy))).1, hface⟩

end Geometry.SimplicialComplex
