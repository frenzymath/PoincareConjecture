import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_CapIntersections
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionRefinement
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.EdgeGeometry














noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface ChartCircleArrangementVertexPatch

namespace PoincareConjecture

private theorem cap_scaled_axes_image {r : ℝ} (hr : 0 < r) :
    (fun t : ℝ => (t * r, (0 : ℝ))) '' Icc 0 1 = Icc 0 r ×ˢ {0} ∧
      (fun t : ℝ => ((0 : ℝ), t * r)) '' Icc 0 1 = {0} ×ˢ Icc 0 r := by
  constructor
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨mul_nonneg ht.1 hr.le, by nlinarith [ht.2]⟩, rfl⟩
    · rintro ⟨hz, hz0⟩
      refine ⟨z.1 / r, ⟨div_nonneg hz.1 hr.le, (div_le_one hr).mpr hz.2⟩, ?_⟩
      exact Prod.ext (div_mul_cancel₀ z.1 hr.ne') (mem_singleton_iff.mp hz0).symm
  · ext z
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨rfl, ⟨mul_nonneg ht.1 hr.le, by nlinarith [ht.2]⟩⟩
    · rintro ⟨hz0, hz⟩
      refine ⟨z.2 / r, ⟨div_nonneg hz.1 hr.le, (div_le_one hr).mpr hz.2⟩, ?_⟩
      exact Prod.ext (mem_singleton_iff.mp hz0).symm (div_mul_cancel₀ z.2 hr.ne')

private theorem cap_compatible_of_full_shared_edge
    (f g : SmoothFace AnnulusCoordinates)
    (C D : OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b c : AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hC : f.carrier = C '' convexHull ℝ (range b))
    (hD : g.carrier = D '' convexHull ℝ (range c))
    (k l : Fin 3)
    (hk : (f.boundary k).map = C ∘ affineChartSegment (b (k.succAbove 0)) (b (k.succAbove 1)))
    (hl : (g.boundary l).map = D ∘ affineChartSegment (c (l.succAbove 0)) (c (l.succAbove 1)))
    (hinter : f.carrier ∩ g.carrier = (f.boundary k).map '' Icc (0 : ℝ) 1)
    (hshared : (f.boundary k).map '' Icc (0 : ℝ) 1 = (g.boundary l).map '' Icc (0 : ℝ) 1) :
    CoordinateTriangleBoundaryIntersection C D b c := by
  apply CoordinateTriangleBoundaryIntersection.subsegment k l 0 1 0 1
    (by simp) (by simp) (by simp) (by simp)
  · simpa only [uIcc_of_le zero_le_one, ← hC, ← hD, ← hk] using hinter
  · simpa only [uIcc_of_le zero_le_one, ← hC, ← hD, ← hl] using hinter.trans hshared






theorem m64Intrinsic_retained_caps_canonical_compatibility
    (H : OpenPartialHomeomorph (ℝ × ℝ) AnnulusCoordinates) {r : ℝ} (hr : 0 < r)
    (face : Bool × Bool → SmoothFace AnnulusCoordinates)
    (C : Bool × Bool → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : Bool × Bool → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = C i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hsector : ∀ i, (face i).carrier ⊆ H '' (H.source ∩ (sectorParameterEquiv 0 i) ''
      {q : ℝ × ℝ | 0 ≤ q.1 ∧ 0 ≤ q.2}))
    (haxes : ∀ i, (face i).carrier ∩
      H '' (H.source ∩ {q : ℝ × ℝ | q.1 = 0 ∨ q.2 = 0}) =
        H '' ((sectorParameterEquiv 0 i) ''
          ((Icc (0 : ℝ) r ×ˢ {0}) ∪ ({0} ×ˢ Icc (0 : ℝ) r))))
    (hsmall : ∀ i : Bool × Bool, ∀ s ∈ Icc (0 : ℝ) r,
      sectorParameterEquiv 0 i (s, 0) ∈ H.source ∧
      sectorParameterEquiv 0 i (0, s) ∈ H.source)
    (hsecond : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 1).map t =
      H (sectorParameterEquiv 0 i (0, t * r)))
    (hfirst : ∀ i, ∀ t ∈ Icc (0 : ℝ) 1, ((face i).boundary 2).map t =
      H (sectorParameterEquiv 0 i (t * r, 0))) :
    ∀ i j, i ≠ j → CoordinateTriangleBoundaryIntersection (C i) (C j) (b i) (b j) := by
  have hfirstimage (i : Bool × Bool) : ((face i).boundary 2).map '' Icc (0 : ℝ) 1 =
      H '' ((sectorParameterEquiv 0 i) '' (Icc (0 : ℝ) r ×ˢ {0})) := by
    calc
      _ = (H ∘ (sectorParameterEquiv 0 i) ∘ (fun t : ℝ => (t * r, 0))) '' Icc 0 1 :=
        image_congr (fun t ht => hfirst i t ht)
      _ = _ := by rw [image_comp, image_comp, (cap_scaled_axes_image hr).1]
  have hsecondimage (i : Bool × Bool) : ((face i).boundary 1).map '' Icc (0 : ℝ) 1 =
      H '' ((sectorParameterEquiv 0 i) '' ({0} ×ˢ Icc (0 : ℝ) r)) := by
    calc
      _ = (H ∘ (sectorParameterEquiv 0 i) ∘ (fun t : ℝ => (0, t * r))) '' Icc 0 1 :=
        image_congr (fun t ht => hsecond i t ht)
      _ = _ := by rw [image_comp, image_comp, (cap_scaled_axes_image hr).2]
  have hhorizontal (i : Bool) :
      CoordinateTriangleBoundaryIntersection (C (i, false)) (C (i, true))
        (b (i, false)) (b (i, true)) := by
    apply cap_compatible_of_full_shared_edge (face _) (face _) _ _ _ _
      (hcarrier _) (hcarrier _) 2 2 (hboundary _ _) (hboundary _ _)
    · exact (m64Intrinsic_neighbor_caps_inter_horizontal H hr.le (fun i => (face i).carrier)
        hsector haxes hsmall i).trans (hfirstimage _).symm
    · apply image_congr
      intro t ht
      rw [hfirst _ t ht, hfirst _ t ht]
      simp [sectorParameterEquiv_apply]
  have hvertical (j : Bool) :
      CoordinateTriangleBoundaryIntersection (C (false, j)) (C (true, j))
        (b (false, j)) (b (true, j)) := by
    apply cap_compatible_of_full_shared_edge (face _) (face _) _ _ _ _
      (hcarrier _) (hcarrier _) 1 1 (hboundary _ _) (hboundary _ _)
    · exact (m64Intrinsic_neighbor_caps_inter_vertical H hr.le (fun i => (face i).carrier)
        hsector haxes hsmall j).trans (hsecondimage _).symm
    · apply image_congr
      intro t ht
      rw [hsecond _ t ht, hsecond _ t ht]
      simp [sectorParameterEquiv_apply]
  have hcorner (i : Bool × Bool) : H 0 ∈ C i '' frontier (convexHull ℝ (range (b i))) := by
    have hzero := hfirst i 0 (by simp)
    have heq : C i (b i 0) = H 0 := by
      change C i (b i 0) = H (0, 0)
      simpa [hboundary, affineChartSegment, sectorParameterEquiv_apply] using hzero
    rw [← heq]
    exact mem_image_of_mem _ (Euler.coordinate_vertices_subset_frontier _ (mem_range_self 0))
  have hopposite (i : Bool × Bool) :
      CoordinateTriangleBoundaryIntersection (C i) (C (!i.1, !i.2)) (b i) (b (!i.1, !i.2)) := by
    apply CoordinateTriangleBoundaryIntersection.point (H 0) (hcorner i) (hcorner (!i.1, !i.2))
    rw [← hcarrier, ← hcarrier,
      m64Intrinsic_opposite_caps_inter H hr.le (fun i => (face i).carrier) hsector haxes i]
  rintro ⟨i, i'⟩ ⟨j, j'⟩ hij
  cases i <;> cases i' <;> cases j <;> cases j'
  all_goals first
    | exact (hij rfl).elim
    | exact hhorizontal false
    | exact (hhorizontal false).symm
    | exact hhorizontal true
    | exact (hhorizontal true).symm
    | exact hvertical false
    | exact (hvertical false).symm
    | exact hvertical true
    | exact (hvertical true).symm
    | exact hopposite (false, false)
    | exact hopposite (false, true)
    | exact hopposite (true, false)
    | exact hopposite (true, true)

end PoincareConjecture
