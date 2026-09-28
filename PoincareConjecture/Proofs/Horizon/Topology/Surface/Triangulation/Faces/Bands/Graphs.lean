import PoincareConjecture.Proofs.Horizon.Topology.Plane.Curves.Graphs.Strip
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Edges.CollarCoordinates
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Triangulation.Faces.Rectangles

set_option autoImplicit false
open Set
open scoped Manifold ContDiff Topology Matrix
open Poincare.Topology.Plane.Curves Poincare.Topology.Plane.Triangles

namespace PoincareConjecture.Topology.Surface

universe u
variable {M : Type u} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M] [IsManifold (𝓡 2) ∞ M]

theorem exists_smoothFace_pair_between_graphs
    (F : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) M)
    (hF : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F F.source)
    (hFinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ F.symm F.target)
    {lo hi : ℝ → ℝ} {U : Set ℝ}
    (hU : IsOpen U) (hlo : ContDiffOn ℝ ∞ lo U) (hhi : ContDiffOn ℝ ∞ hi U)
    (hgap : ∀ t ∈ U, lo t < hi t)
    {a b : ℝ} (hab : a < b) (hI : Icc a b ⊆ U)
    (hband : collarParameterEquiv ⁻¹'
      {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1} ⊆ F.source)
    (p : M) (hchart : F.target ⊆ (chartAt (EuclideanSpace ℝ (Fin 2)) p).source) :
    ∃ f g : SmoothFace M,
      f.map = (fun z => F (collarParameterEquiv.symm
        (graphStripMap lo hi (collarParameterEquiv z)))) ∧
      g.map = f.map ∧
      f.source = convexHull ℝ (range (rectangleLowerBasis hab zero_lt_one)) ∧
      g.source = convexHull ℝ (range (rectangleUpperBasis hab zero_lt_one)) ∧
      InjOn f.map f.source ∧ InjOn g.map g.source ∧
      f.carrier ∪ g.carrier = F '' (collarParameterEquiv ⁻¹'
        {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}) ∧
      f.carrier ∩ g.carrier = (f.boundary 1).map '' Icc (0 : ℝ) 1 ∧
      f.boundary 1 = g.boundary 1 ∧
      (∀ t : ℝ, (f.boundary 2).map t =
        F (collarParameterEquiv.symm (a + t * (b - a), lo (a + t * (b - a))))) ∧
      (∀ t : ℝ, (g.boundary 0).map t =
        F (collarParameterEquiv.symm (a + t * (b - a), hi (a + t * (b - a))))) ∧
      (∀ t : ℝ, (f.boundary 0).map t =
        F (collarParameterEquiv.symm (b, lo b + t * (hi b - lo b)))) ∧
      (∀ t : ℝ, (g.boundary 2).map t =
        F (collarParameterEquiv.symm (a, lo a + t * (hi a - lo a)))) := by
  let L := collarParameterEquiv
  let G := graphStripCoordinates hU hlo hhi hgap
  let H := (L.toHomeomorph.toOpenPartialHomeomorph.trans G).trans
    L.symm.toHomeomorph.toOpenPartialHomeomorph
  let C := H.trans F
  have hG : ContDiffOn ℝ ∞ G G.source := contDiffOn_graphStripMap hlo hhi
  have hGinv : ContDiffOn ℝ ∞ G.symm G.target := contDiffOn_graphStripInv hlo hhi hgap
  have hH : ContDiffOn ℝ ∞ H H.source :=
    L.symm.contDiff.comp_contDiffOn
      ((hG.comp L.contDiff.contDiffOn (fun _ hz => hz.1.2)))
  have hHinv : ContDiffOn ℝ ∞ H.symm H.target :=
    L.symm.contDiff.comp_contDiffOn
      (hGinv.comp L.contDiff.contDiffOn (fun _ hz => hz.2.1))
  have hC : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C C.source :=
    hF.comp (hH.contMDiffOn.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  have hCinv : ContMDiffOn (𝓡 2) (𝓡 2) ∞ C.symm C.target :=
    hHinv.contMDiffOn.comp (hFinv.mono (fun _ hz => hz.1)) (fun _ hz => hz.2)
  let R : Set (EuclideanSpace ℝ (Fin 2)) := {z | z 0 ∈ Icc a b ∧ z 1 ∈ Icc (0 : ℝ) 1}
  let B : Set (EuclideanSpace ℝ (Fin 2)) := L ⁻¹'
    {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
  have himage : H '' R = B := by
    have heq := graphStripMap_image_rectangle (fun t ht => hgap t (hI ht))
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      change L (L.symm (graphStripMap lo hi (L w))) ∈
        {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1}
      rw [L.apply_symm_apply, ← heq]
      exact ⟨L w, hw, rfl⟩
    · intro hz
      change L z ∈ {q : ℝ × ℝ | q.1 ∈ Icc a b ∧ lo q.1 ≤ q.2 ∧ q.2 ≤ hi q.1} at hz
      rw [← heq] at hz
      obtain ⟨q, hq, he⟩ := hz
      refine ⟨L.symm q, ?_, ?_⟩
      · change L (L.symm q) ∈ Icc a b ×ˢ Icc (0 : ℝ) 1
        simpa only [L.apply_symm_apply] using hq
      · change L.symm (graphStripMap lo hi (L (L.symm q))) = z
        rw [L.apply_symm_apply, he, L.symm_apply_apply]
  have hrect : R ⊆ C.source := by
    intro z hz
    refine ⟨⟨⟨mem_univ _, ?_⟩, mem_univ _⟩, ?_⟩
    · exact ⟨hI hz.1, mem_univ _⟩
    · apply hband
      change H z ∈ B
      rw [← himage]
      exact mem_image_of_mem H hz
  obtain ⟨f, g, hf, hg, hfs, hgs, hfi, hgi, hcover, hinter, hdiag, hlower, hfedge, hgedge⟩ :=
    exists_smoothFace_pair_of_coordinate_rectangle_with_boundaries C hC hCinv hab zero_lt_one
      hrect p (fun _ hz => hchart hz.1)
  refine ⟨f, g, hf, hg.trans hf.symm, hfs, hgs, hfi, hgi, ?_, hinter, hdiag, ?_, ?_, ?_, ?_⟩
  · rw [hcover]
    change (F ∘ H) '' R = F '' B
    calc
      (F ∘ H) '' R = F '' (H '' R) := (image_image F H R).symm
      _ = F '' B := congrArg (fun S => F '' S) himage
  · intro t
    rw [hlower]
    change F (L.symm (graphStripMap lo hi (a + t * (b - a), 0))) = _
    rw [graphStripMap_lower]
  · intro t
    rw [hgedge 0]
    change F (L.symm (graphStripMap lo hi
      (L (affineChartSegment _ _ t)))) = _
    have he : L (affineChartSegment
        (rectangleUpperBasis hab zero_lt_one (Fin.succAbove 0 0))
        (rectangleUpperBasis hab zero_lt_one (Fin.succAbove 0 1)) t) =
        (a + t * (b - a), 1) := by
      change L (affineChartSegment !₂[a, 1] !₂[b, 1] t) = _
      ext <;> simp [L, affineChartSegment]
    rw [he, graphStripMap_upper]
  · intro t
    rw [hfedge 0]
    change F (L.symm (graphStripMap lo hi
      (L (affineChartSegment _ _ t)))) = _
    have he : L (affineChartSegment
        (rectangleLowerBasis hab zero_lt_one (Fin.succAbove 0 0))
        (rectangleLowerBasis hab zero_lt_one (Fin.succAbove 0 1)) t) = (b, t) := by
      change L (affineChartSegment !₂[b, 0] !₂[b, 1] t) = _
      ext <;> simp [L, affineChartSegment]
    rw [he]
    rfl
  · intro t
    rw [hgedge 2]
    change F (L.symm (graphStripMap lo hi
      (L (affineChartSegment _ _ t)))) = _
    have he : L (affineChartSegment
        (rectangleUpperBasis hab zero_lt_one (Fin.succAbove 2 0))
        (rectangleUpperBasis hab zero_lt_one (Fin.succAbove 2 1)) t) = (a, t) := by
      change L (affineChartSegment !₂[a, 0] !₂[a, 1] t) = _
      ext <;> simp [L, affineChartSegment]
    rw [he]
    rfl

end PoincareConjecture.Topology.Surface
