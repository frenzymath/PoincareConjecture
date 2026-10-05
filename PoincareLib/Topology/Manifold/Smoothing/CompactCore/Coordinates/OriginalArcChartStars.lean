import PoincareLib.Topology.Manifold.Smoothing.CompactCore.Coordinates.OriginalArcCharts
import PoincareLib.Topology.Manifold.Smoothing.PrimeReduction.Coordinates.CompatibleChartStars

/-!
# Whole finite stars in the actual original arc pair charts

One simultaneous refinement retains all finite marks and places
every complete arc-vertex star in a constructed original pair chart.
An off-arc chart cannot contain such a vertex, so the full protected
source and line or ray equations survive the finite selection.
See Hudson 1969, pp. 12--19 and Wall013, section 3.
-/

set_option autoImplicit false

open Set Geometry

namespace PoincareMT.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

/-- The actual original arc charts construct a full marked
subdivision with whole closed-star source inclusion and affine
coordinate formulas. Every arc-vertex star inherits the exact
protected line or endpoint-ray equation; no graph-interior or
star-chart premise is supplied. See013, section 3. -/
theorem PLDomain.exists_original_arc_chart_stars
    {X E ι κ : Type*} [TopologicalSpace X] [T2Space X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [DecidableEq E] [Finite κ]
    {e : ι → OpenPartialHomeomorph X V3} {L : Set X} (he : PLDomain e L)
    {q : ℝ → X} (hq : PolyhedralPLInCharts e q I) (hqi : InjOn q I)
    (hzero : q 0 ∈ frontier L) (hone : q 1 ∈ frontier L)
    (hproper : ∀ t ∈ Ioo (0 : ℝ) 1, q t ∉ L)
    {W : Set X} (hW : IsOpen W) (hqW : MapsTo q I W)
    (U : Fin 2 → Set X) (hU : ∀ i, IsOpen (U i))
    (hU0 : q 0 ∈ U 0) (hU1 : q 1 ∈ U 1)
    (K : SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space)
    (A : κ → SimplicialComplex ℝ E) (hA : ∀ i, (A i).faces.Finite)
    (hAK : ∀ i, (A i).space ⊆ K.space) (a : κ)
    (hAa : MapsTo f (A a).space (q '' I)) :
    ∃ (R : SimplicialComplex ℝ E) (B : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, B i ≤ R ∧ (B i).space = (A i).space ∧
        ∀ t ∈ R.faces, (∀ v ∈ t, v ∈ (B i).vertices) → t ∈ (B i).faces) ∧
      ∀ p ∈ (B a).vertices, ∃ G : OpenPartialHomeomorph X V3,
        MapsTo f (R.closedStar p).space G.source ∧
        (R.closedStar p).AffineOnFaces (G ∘ f) ∧
        (∀ i, (e i).symm.trans G ∈ piecewiseAffineGroupoid V3) ∧ G.source ⊆ W ∧
        ((G.source ⊆ Lᶜ ∧ ∃ v : V3, v ≠ 0 ∧
          ∀ y ∈ G.source, y ∈ q '' I ↔ ∃ r : ℝ, G y = r • v) ∨
        ∃ (i : Fin 2) (A : V3 →L[ℝ] ℝ) (v : V3),
          G.source ⊆ U i ∧ A v = 1 ∧
          (∀ y ∈ G.source, y ∈ L ↔ 0 ≤ A (G y)) ∧
          (∀ y ∈ G.source, y ∈ frontier L ↔ A (G y) = 0) ∧
          ∀ y ∈ G.source,
            y ∈ q '' I ↔ ∃ r : ℝ, r ≤ 0 ∧ G y = r • v) := by
  classical
  choose G hpoint hcompat hcase using fun x : X =>
    he.exists_original_arc_model_chart hq hqi hzero hone hproper hW hqW U hU hU0 hU1 x
  obtain ⟨R, B, hR, hRK, hB, hstars⟩ :=
    hf.exists_full_compatible_chart_stars K hK (fun z => G (f z))
      (fun z => hcompat (f z)) (fun z => hpoint (f z)) A hA hAK
  refine ⟨R, B, hR, hRK, hB, ?_⟩
  intro p hp
  have hpR : p ∈ R.vertices := (hB a).1 hp
  have hpstar : p ∈ (R.closedStar p).space := by
    apply (R.closedStar p).vertices_subset_space
    change {p} ∈ R.faces ∧ insert p {p} ∈ R.faces
    exact ⟨hpR, by simpa only [Finset.insert_eq_of_mem (Finset.mem_singleton_self p)]
      using (show {p} ∈ R.faces from hpR)⟩
  have hparc : f p ∈ q '' I :=
    hAa ((hB a).2.1.subset ((B a).vertices_subset_space hp))
  obtain ⟨z, hsource, hface⟩ := hstars p hpR
  rcases hcase (f z) with hmiss | ⟨hGW, hpair⟩
  · exact False.elim ((hmiss (hsource hpstar)) hparc)
  · exact ⟨G (f z), hsource, hface, hcompat (f z), hGW, hpair⟩

end PoincareMT.M76
