import PoincareConjecture.Proofs.M76.Wall.OriginalArcChartStars
import PoincareConjecture.Proofs.M76.Wall.Mathlib.ArcFaceDimension
import PoincareConjecture.Proofs.M76.Mathlib.EmbeddedSubcomplexCarriers

set_option autoImplicit false

open Set Geometry Geometry.SimplicialComplex

namespace PoincareConjecture.M76

local notation "V3" => (Fin 3 → ℝ)
local notation "I" => Icc (0 : ℝ) 1

theorem PLDomain.exists_original_arc_complex_dimension
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
    {f : E → X} (hf : PolyhedralPLInCharts e f K.space) (hfi : InjOn f K.space)
    (A : κ → SimplicialComplex ℝ E) (hA : ∀ i, (A i).faces.Finite)
    (hAK : ∀ i, (A i).space ⊆ K.space) (a : κ)
    (hAa : MapsTo f (A a).space (q '' I)) :
    ∃ (R : SimplicialComplex ℝ E) (B : κ → SimplicialComplex ℝ E),
      R.faces.Finite ∧ R.IsSubdivision K ∧
      (∀ i, B i ≤ R ∧ (B i).space = (A i).space ∧
        ∀ t ∈ R.faces, (∀ v ∈ t, v ∈ (B i).vertices) → t ∈ (B i).faces) ∧
      (∀ s ∈ (B a).faces, s.card ≤ 2) ∧
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
  obtain ⟨R, B, hR, hRK, hB, hstars⟩ :=
    he.exists_original_arc_chart_stars hq hqi hzero hone hproper hW hqW U hU hU0 hU1
      K hK hf A hA hAK a hAa
  have hfiR : InjOn f R.space := hfi.mono hRK.space_eq.subset
  have hBa : MapsTo f (B a).space (q '' I) := hAa.mono_left (hB a).2.1.subset
  refine ⟨R, B, hR, hRK, hB, ?_, hstars⟩
  intro s hs
  obtain ⟨p, hps⟩ := (B a).nonempty_of_mem_faces hs
  have hp : p ∈ (B a).vertices :=
    (B a).down_closed hs (Finset.singleton_subset_iff.mpr hps) (Finset.singleton_nonempty p)
  have hsR : s ∈ R.faces := (hB a).1 hs
  have hsstar : s ∈ (R.closedStar p).faces :=
    ⟨hsR, by simpa only [Finset.insert_eq_of_mem hps] using hsR⟩
  have hstarR : R.closedStar p ≤ R := fun _ ht => ht.1
  obtain ⟨G, hsource, hface, _, _, hpair⟩ := hstars p hp
  have hcomp : InjOn (G ∘ f) (R.closedStar p).space := by
    intro x hx y hy hxy
    exact hfiR (space_subset_of_le hstarR hx) (space_subset_of_le hstarR hy)
      (G.injOn (hsource hx) (hsource hy) hxy)
  have hxstar (x : E) (hx : x ∈ s) : x ∈ (R.closedStar p).space :=
    (R.closedStar p).convexHull_subset_space hsstar (subset_convexHull ℝ _ hx)
  have hxarc (x : E) (hx : x ∈ s) : f x ∈ q '' I :=
    hBa ((B a).convexHull_subset_space hs (subset_convexHull ℝ _ hx))
  rcases hpair with ⟨_, v, _, hline⟩ | ⟨i, A, v, _, _, _, _, hray⟩
  · apply hface.face_card_le_two_of_line hcomp hsstar v
    intro x hx
    exact (hline (f x) (hsource (hxstar x hx))).mp (hxarc x hx)
  · apply hface.face_card_le_two_of_line hcomp hsstar v
    intro x hx
    obtain ⟨r, _, hr⟩ := (hray (f x) (hsource (hxstar x hx))).mp (hxarc x hx)
    exact ⟨r, hr⟩

end PoincareConjecture.M76
