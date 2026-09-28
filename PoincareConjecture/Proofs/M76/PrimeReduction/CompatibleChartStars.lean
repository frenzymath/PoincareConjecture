import PoincareConjecture.Proofs.M76.PrimeReduction.RelativeChartStars
import PoincareConjecture.Proofs.M76.Rigidity.CompatibleChartPatch










set_option autoImplicit false

open Set

namespace Geometry

variable {E V X ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace X] [Finite κ]
  {e : ι → OpenPartialHomeomorph X V}




theorem PolyhedralPLInCharts.exists_full_compatible_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (G : K.space → OpenPartialHomeomorph X V)
    (hcompat : ∀ q i, (e i).symm.trans (G q) ∈ piecewiseAffineGroupoid V)
    (hpoint : ∀ q : K.space, f q ∈ (G q).source)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L a).vertices) → s ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, ∃ q : K.space,
        MapsTo f (R.closedStar p).space (G q).source ∧
        (R.closedStar p).AffineOnFaces (G q ∘ f) := by
  classical
  choose N W _ hNK hW hxW hWN hNG hcoords using fun q : K.space =>
    hf.exists_finite_compatible_chart_patch K hK (G q) (hcompat q) q (hpoint q)
  let : CompactSpace K.space :=
    isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun q _ => mem_iUnion.mpr ⟨q, hxW q⟩)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_relative_chart_stars hK J hJ hJK
      (fun q : t => N q) (fun q => hNK q) (fun q : t => W q) (fun q => hW q)
      (by
        intro x
        obtain ⟨q, hqt, hq⟩ := mem_iUnion₂.mp (ht (mem_univ x))
        exact ⟨⟨q, hqt⟩, hq⟩)
      (fun q => hWN q) (fun q : t => G q ∘ f) (fun q => hcoords q)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp
  obtain ⟨q, _, hsub, hface⟩ := hstars p hp
  exact ⟨q, fun _ hx => hNG q (hsub hx), hface⟩

end Geometry
