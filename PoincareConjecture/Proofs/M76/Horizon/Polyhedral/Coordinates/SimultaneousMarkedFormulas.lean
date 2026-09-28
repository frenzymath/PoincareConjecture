import PoincareConjecture.Proofs.M76.Mathlib.FinitePLFullChartStars










set_option autoImplicit false

open Set

namespace Geometry.SimplicialComplex

theorem exists_simultaneous_marked_formulas
    {E F ι κ : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] [Finite ι] [Finite κ]
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    (J : ι → SimplicialComplex ℝ E) (hJ : ∀ i, (J i).faces.Finite)
    (hJK : ∀ i, (J i).space ⊆ K.space)
    (f : ι → E → F) (hf : ∀ i, FinitePiecewiseAffineOn (f i) (J i).space)
    (P : κ → SimplicialComplex ℝ E) (hP : ∀ j, (P j).faces.Finite)
    (hPK : ∀ j, (P j).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : ι → SimplicialComplex ℝ E)
      (Q : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, L i ≤ R ∧ (L i).space = (J i).space ∧
        (∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L i).vertices) → s ∈ (L i).faces) ∧
        (L i).AffineOnFaces (f i)) ∧
      ∀ j, Q j ≤ R ∧ (Q j).space = (P j).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (Q j).vertices) → s ∈ (Q j).faces := by
  classical
  let : Fintype ι := Fintype.ofFinite ι
  choose g hg hgf _ _ using fun i =>
    (hf i).exists_supported_extension K hK (hJK i) isOpen_univ (subset_univ _)
  obtain ⟨T, hT, hTK, hgT⟩ := FinitePiecewiseAffineOn.pi_on_complex K hK hg
  obtain ⟨S, hS, hSK, hST⟩ := K.exists_common_finite_subdivision T hK hT hTK.symm
  let M : Sum ι κ → SimplicialComplex ℝ E := Sum.elim J P
  have hM (a : Sum ι κ) : (M a).faces.Finite := by
    cases a with
    | inl i => exact hJ i
    | inr j => exact hP j
  have hMS (a : Sum ι κ) : (M a).space ⊆ S.space := by
    rw [hSK.space_eq]
    cases a with
    | inl i => exact hJK i
    | inr j => exact hPK j
  obtain ⟨R, L, hR, hRS, hL⟩ :=
    S.exists_subdivision_with_finite_full_polyhedra hS M hM hMS
  have hgR (i : ι) : R.AffineOnFaces (g i) :=
    ((hRS.trans hST).affineOnFaces hgT).postcomp
      (ContinuousLinearMap.proj i : (ι → F) →L[ℝ] F).toContinuousAffineMap
  refine ⟨R, fun i => L (.inl i), fun j => L (.inr j), hR, hRS.trans hSK, ?_,
    fun j => hL (.inr j)⟩
  intro i
  refine ⟨(hL (.inl i)).1, (hL (.inl i)).2.1, (hL (.inl i)).2.2, ?_⟩
  have hlocal : (L (.inl i)).AffineOnFaces (g i) :=
    fun s hs => hgR i s ((hL (.inl i)).1 hs)
  apply hlocal.congr
  intro x hx
  exact hgf i ((hL (.inl i)).2.1.subset hx)

end Geometry.SimplicialComplex
