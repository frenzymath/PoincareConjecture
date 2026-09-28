import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalBranchTargetComplex
import PoincareConjecture.Proofs.M76.Horizon.Dehn.Annuli.Surgery.Tubes.Branches.Transition

set_option autoImplicit false
open Set Metric Geometry Topology Geometry.SimplicialComplex

namespace PoincareConjecture.M76.Dehn.Annuli

local notation "V3" => (Fin 3 → ℝ)
local notation "P2" => (ℝ × ℝ)

open Classical in
theorem ComponentBranchModel.exists_marked_raw_star
    {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace X] {S : Set E}
    {e : ι → OpenPartialHomeomorph X V3} {f : E → X} {R : Set X}
    {old : SourceCircleDecomposition f S} {i : old.Index}
    (D : ComponentBranchModel (e := e) (R := R) old i)
    (p : D.sample → ℝ × V3) (hp : p ∈ D.axis.vertices) :
    ∃ (x y : E) (C : RawSourceCrossing e f S R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      ∀ j : Fin 2,
        ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar p).space ∩
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0} := by
  classical
  obtain ⟨q, hmap, hface⟩ := D.selected_stars p hp
  obtain ⟨x, y, C, _, hB, hBC⟩ := D.raw_charts q
  let K := D.complex.closedStar p
  have hKD : K ≤ D.complex := fun _ hs => hs.1
  have hKs := SimplicialComplex.space_subset_of_le hKD
  have hKC : MapsTo (fun z ↦ (D.inverse z : X)) K.space C.chart.source :=
    fun _ hz => hBC (hmap hz)
  have hCface : K.AffineOnFaces (fun z ↦ C.chart (D.inverse z)) := by
    simpa only [hB] using hface
  have hUspace := D.complex.space_inf_eq_inter_of_le D.sourceImage K D.sourceImage_le hKD
  have hAspace := D.complex.space_inf_eq_inter_of_le D.axis K D.axis_le hKD
  have hfull : ∀ s ∈ K.faces,
      (∀ v ∈ s, v ∈ (D.sourceImage ⊓ K).vertices) → s ∈ (D.sourceImage ⊓ K).faces := by
    intro s hs hv
    exact ⟨D.sourceImage_full s (hKD hs) (fun v hvs => (hv v hvs).1), hs⟩
  have haxis (z : D.sample → ℝ × V3) (hz : z ∈ K.space) :
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ f '' old.pieces i := by
    rw [D.axis_space]
    constructor
    · rintro ⟨a, ha, haz⟩
      refine ⟨a, ha, ?_⟩
      exact (D.graph_separates _ (D.inverse z).property _
        ((D.graph_inverse z (hKs hz)).trans haz.symm)).symm
    · rintro ⟨a, ha, haz⟩
      refine ⟨a, ha, ?_⟩
      change D.graph (f a) = z
      rw [haz, D.graph_inverse z (hKs hz)]
  have hCA (z : D.sample → ℝ × V3) (hz : z ∈ K.space) :
      z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
        C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0 := by
    rw [haxis z hz]
    simpa only [hB] using D.chart_axis q (D.inverse z) (hmap hz)
  refine ⟨x, y, C, hKC, hCface, hCA, fun j => ?_⟩
  apply local_crossing_vertexSubcomplex_space K (D.sourceImage ⊓ K) (D.axis ⊓ K)
    (SimplicialComplex.finite_closedStar_faces D.complex_finite p)
    inf_le_right inf_le_right hfull hCface {z | (D.inverse z : X) ∈ R}
  · intro z hz
    rw [hUspace, mem_inter_iff, and_iff_left hz, D.mem_sourceImage z (hKs hz)]
    exact C.source_image_iff _ (hKC hz)
  · intro z hz
    rw [hAspace, mem_inter_iff, and_iff_left hz]
    exact hCA z hz

end PoincareConjecture.M76.Dehn.Annuli
