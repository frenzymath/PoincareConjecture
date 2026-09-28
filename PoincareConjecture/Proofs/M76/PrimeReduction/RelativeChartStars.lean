import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFullChartStars

set_option autoImplicit false

open Set Metric

namespace Geometry.SimplicialComplex

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {ι κ : Type*} [Finite ι] [Finite κ]

theorem exists_full_subcomplex_faceAffine_relative_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space)
    (N : ι → SimplicialComplex ℝ E)
    (hNK : ∀ i, (N i).space ⊆ K.space)
    (W : ι → Set K.space) (hW : ∀ i, IsOpen (W i))
    (hcover : ∀ x : K.space, ∃ i, x ∈ W i)
    (hWN : ∀ i, Subtype.val '' W i ⊆ (N i).space)
    (f : ι → E → F) (hf : ∀ i, FinitePiecewiseAffineOn (f i) (N i).space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L a).vertices) → s ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, ∃ i,
        (∀ x : K.space, (x : E) ∈ (R.closedStar p).space → x ∈ W i) ∧
        (R.closedStar p).space ⊆ (N i).space ∧
        (R.closedStar p).AffineOnFaces (f i) := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose g hg hgf _ _ using fun i =>
    (hf i).exists_supported_extension K hK (hNK i) isOpen_univ (subset_univ _)
  obtain ⟨T, hT, hTK, hgT⟩ := FinitePiecewiseAffineOn.pi_on_complex K hK hg
  obtain ⟨S, hS, hSK, hST⟩ := K.exists_common_finite_subdivision T hK hT hTK.symm
  have hgS (i : ι) : S.AffineOnFaces (g i) :=
    (hST.affineOnFaces hgT).postcomp
      (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).toContinuousAffineMap
  obtain ⟨delta, hdelta, hstars⟩ := K.exists_mesh_for_subdivision_stars hK W hW hcover
  let n := hS.toFinset.sup Finset.card
  have hn (s : Finset E) (hs : s ∈ S.faces) : s.card ≤ n + 1 :=
    (Finset.le_sup (hS.mem_toFinset.mpr hs)).trans (Nat.le_succ n)
  obtain ⟨A, hA, hAS, _, hdiam⟩ := S.exists_finite_subdivision_mesh hS hn hdelta
  have hAK := hAS.trans hSK
  obtain ⟨R, L, hR, hRA, hL⟩ := A.exists_subdivision_with_finite_full_polyhedra hA J hJ
    (fun a x hx => hAK.space_eq.symm.subset (hJK a hx))
  have hRK := hRA.trans hAK
  have hRdiam (s : Finset E) (hs : s ∈ R.faces) :
      diam (convexHull ℝ (s : Set E)) ≤ delta := by
    obtain ⟨t, ht, hst⟩ := hRA.face_subset s hs
    exact (diam_mono hst (t.finite_toSet.isCompact_convexHull ℝ).isBounded).trans
      (hdiam t ht)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp
  have hstar : R.closedFaceStar {p} = R.closedStar p := by
    ext s
    simp only [closedFaceStar, closedStar, Finset.singleton_union]
  obtain ⟨i, hi⟩ := hstars R hRK hRdiam p hp
  have hWi (x : K.space) (hx : (x : E) ∈ (R.closedStar p).space) : x ∈ W i :=
    hi x (hstar.symm ▸ hx)
  have hsub : (R.closedStar p).space ⊆ (N i).space := by
    intro x hx
    have hxR : x ∈ R.space := by
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hx
      exact R.convexHull_subset_space hs.1 hxs
    let xK : K.space := ⟨x, hRK.space_eq.subset hxR⟩
    exact hWN i ⟨xK, hWi xK hx, rfl⟩
  have hgR : R.AffineOnFaces (g i) := (hRA.trans hAS).affineOnFaces (hgS i)
  refine ⟨i, hWi, hsub, ?_⟩
  exact (show (R.closedStar p).AffineOnFaces (g i) from
    fun s hs => hgR s hs.1).congr (fun x hx => hgf i (hsub hx))

end Geometry.SimplicialComplex
