import PoincareConjecture.Proofs.M76.PrimeReduction.CompatibleChartStars
import PoincareConjecture.Proofs.M76.Mathlib.FinitePLArithmetic

set_option autoImplicit false
open Set

namespace Geometry

variable {E V X ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [DecidableEq E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace X] [Finite κ]
  {e : ι → OpenPartialHomeomorph X V}

theorem PolyhedralPLInCharts.exists_full_simultaneous_compatible_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (G H : K.space → OpenPartialHomeomorph X V)
    (hG : ∀ q i, (e i).symm.trans (G q) ∈ piecewiseAffineGroupoid V)
    (hH : ∀ q i, (e i).symm.trans (H q) ∈ piecewiseAffineGroupoid V)
    (hpG : ∀ q : K.space, f q ∈ (G q).source)
    (hpH : ∀ q : K.space, f q ∈ (H q).source)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ s ∈ R.faces, (∀ v ∈ s, v ∈ (L a).vertices) → s ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, ∃ q : K.space,
        MapsTo f (R.closedStar p).space (G q).source ∧
        (R.closedStar p).AffineOnFaces (G q ∘ f) ∧
        MapsTo f (R.closedStar p).space (H q).source ∧
        (R.closedStar p).AffineOnFaces (H q ∘ f) := by
  classical
  choose NG WG hNG hNGK hWG hxWG hWGNG hNGG hcoordsG using fun q : K.space =>
    hf.exists_finite_compatible_chart_patch K hK (G q) (hG q) q (hpG q)
  choose NH WH hNH hNHK hWH hxWH hWHNH hNHH hcoordsH using fun q : K.space =>
    hf.exists_finite_compatible_chart_patch K hK (H q) (hH q) q (hpH q)
  choose N W hN hNK hW hxW hWN hNO using fun q : K.space =>
    K.exists_relative_polyhedral_neighborhood hK q ((hWG q).inter (hWH q))
      ⟨hxWG q, hxWH q⟩
  have hsubG (q : K.space) : (N q).space ⊆ (NG q).space := by
    intro y hy
    exact hWGNG q ⟨⟨y, hNK q hy⟩, (hNO q hy).1, rfl⟩
  have hsubH (q : K.space) : (N q).space ⊆ (NH q).space := by
    intro y hy
    exact hWHNH q ⟨⟨y, hNK q hy⟩, (hNO q hy).2, rfl⟩
  have hcoords (q : K.space) :
      FinitePiecewiseAffineOn (fun y => ((G q) (f y), (H q) (f y))) (N q).space :=
    ((hcoordsG q).restrict (N q) (hN q) (hsubG q)).prod_mk
      ((hcoordsH q).restrict (N q) (hN q) (hsubH q))
  let : CompactSpace K.space := isCompact_iff_compactSpace.mp (K.isCompact_space_of_finite hK)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover W hW
    (fun q _ => mem_iUnion.mpr ⟨q, hxW q⟩)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_relative_chart_stars hK J hJ hJK
      (fun q : t => N q) (fun q => hNK q) (fun q : t => W q) (fun q => hW q)
      (by
        intro x
        obtain ⟨q, hqt, hq⟩ := mem_iUnion₂.mp (ht (mem_univ x))
        exact ⟨⟨q, hqt⟩, hq⟩)
      (fun q => hWN q) (fun q : t => fun y => ((G q) (f y), (H q) (f y)))
      (fun q => hcoords q)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp
  obtain ⟨q, _, hsub, hface⟩ := hstars p hp
  exact ⟨q, fun _ hx => hNGG q (hsubG q (hsub hx)),
    hface.postcomp (ContinuousLinearMap.fst ℝ V V).toContinuousAffineMap,
    fun _ hx => hNHH q (hsubH q (hsub hx)),
    hface.postcomp (ContinuousLinearMap.snd ℝ V V).toContinuousAffineMap⟩

end Geometry
