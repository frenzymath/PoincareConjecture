import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MixedCompatibleChartPatch
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.RelativeMarkedChartStars











set_option autoImplicit false

open Set

namespace Geometry

variable {E V W X ι κ : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [DecidableEq E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [TopologicalSpace X] [Finite κ] {e : ι → OpenPartialHomeomorph X V}





theorem PolyhedralPLInCharts.exists_full_marked_mixed_chart_stars
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    {S : Set E} (hS : IsCompact S) (hSK : S ⊆ K.space)
    (G : S → OpenPartialHomeomorph X W)
    (hcompat : ∀ q i, LocallyPiecewiseAffineOn
      ((e i).symm.trans (G q)) ((e i).symm.trans (G q)).source)
    (hpoint : ∀ q : S, f q ∈ (G q).source)
    (U : S → Set K.space) (hU : ∀ q, IsOpen (U q))
    (hxU : ∀ q : S, (⟨q, hSK q.property⟩ : K.space) ∈ U q)
    (J : κ → SimplicialComplex ℝ E) (hJ : ∀ a, (J a).faces.Finite)
    (hJK : ∀ a, (J a).space ⊆ K.space) :
    ∃ (R : SimplicialComplex ℝ E) (L : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ a, L a ≤ R ∧ (L a).space = (J a).space ∧
        ∀ t ∈ R.faces, (∀ v ∈ t, v ∈ (L a).vertices) → t ∈ (L a).faces) ∧
      ∀ p ∈ R.vertices, p ∈ S → ∃ q : S,
        (∀ x : K.space, (x : E) ∈ (R.closedStar p).space → x ∈ U q) ∧
        MapsTo f (R.closedStar p).space (G q).source ∧
        (R.closedStar p).AffineOnFaces (G q ∘ f) := by
  classical
  let k : S → K.space := fun x => ⟨x, hSK x.property⟩
  have hk : Continuous k := continuous_subtype_val.subtype_mk _
  choose N W0 _ hNK hW0 hxW0 hWN hNG hcoords using fun q : S =>
    hf.exists_finite_mixed_chart_patch K hK (G q) (hcompat q) (k q) (hpoint q)
  let W1 (q : S) : Set K.space := W0 q ∩ U q
  have hW1 (q : S) : IsOpen (W1 q) := (hW0 q).inter (hU q)
  have hxW1 (q : S) : k q ∈ W1 q := ⟨hxW0 q, hxU q⟩
  let : CompactSpace S := isCompact_iff_compactSpace.mp hS
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun q => k ⁻¹' W1 q)
    (fun q => (hW1 q).preimage hk) (fun q _ => mem_iUnion.mpr ⟨q, hxW1 q⟩)
  obtain ⟨R, L, hR, hRK, hL, hstars⟩ :=
    K.exists_full_subcomplex_faceAffine_marked_relative_stars hK J hJ hJK hS.isClosed
      (fun q : t => N q) (fun q => hNK q) (fun q : t => W1 q) (fun q => hW1 q)
      (by
        intro x hx
        obtain ⟨q, hqt, hq⟩ := mem_iUnion₂.mp (ht (mem_univ (⟨x, hx⟩ : S)))
        exact ⟨⟨q, hqt⟩, hq⟩)
      (by
        intro q y hy
        obtain ⟨x, hx, rfl⟩ := hy
        exact hWN q ⟨x, hx.1, rfl⟩)
      (fun q : t => G q ∘ f) (fun q => hcoords q)
  refine ⟨R, L, hR, hRK, hL, ?_⟩
  intro p hp hpS
  obtain ⟨q, hqW, hqN, hqf⟩ := hstars p hp hpS
  exact ⟨q, fun x hx => (hqW x hx).2, fun _ hx => hNG q (hqN hx), hqf⟩

end Geometry
