import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.Triangulation
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.CanonicalEdgeSlots
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.GaussBonnet.VertexContributions
import PoincareConjecture.Proofs.Horizon.Topology.Surface.Euler.Count

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle

noncomputable section
open Classical

namespace PoincareConjecture.Topology.Surface

private theorem sum_slots_eq_zero_of_two_faces {I E : Type*} [Fintype I] [Fintype E]
    (slot : I → Fin 3 → E) (hinj : ∀ i, Function.Injective (slot i))
    (adjacent : E → I × I) (hdistinct : ∀ e, (adjacent e).1 ≠ (adjacent e).2)
    (hexact : ∀ e i, (∃ k, slot i k = e) ↔
      i = (adjacent e).1 ∨ i = (adjacent e).2)
    (term : I → Fin 3 → ℝ)
    (hpair : ∀ i j k l, i ≠ j → slot i k = slot j l → term i k + term j l = 0) :
    (∑ i, ∑ k : Fin 3, term i k) = 0 := by
  let f : I × Fin 3 → E := fun p => slot p.1 p.2
  have hfiber (e : E) : (∑ p : {p : I × Fin 3 // f p = e}, term p.1.1 p.1.2) = 0 := by
    obtain ⟨k, hk⟩ := (hexact e (adjacent e).1).mpr (Or.inl rfl)
    obtain ⟨l, hl⟩ := (hexact e (adjacent e).2).mpr (Or.inr rfl)
    let a : {p : I × Fin 3 // f p = e} := ⟨((adjacent e).1, k), hk⟩
    let b : {p : I × Fin 3 // f p = e} := ⟨((adjacent e).2, l), hl⟩
    have hab : a ≠ b := fun h => hdistinct e (congrArg (fun p => p.1.1) h)
    have huniv : (Finset.univ : Finset {p : I × Fin 3 // f p = e}) = {a, b} := by
      ext p
      simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
      rcases (hexact e p.1.1).mp ⟨p.1.2, p.2⟩ with hp | hp
      · left
        apply Subtype.ext
        apply Prod.ext hp
        apply hinj (adjacent e).1
        have he : slot p.1.1 p.1.2 = e := p.2
        rw [hp] at he
        exact he.trans hk.symm
      · right
        apply Subtype.ext
        apply Prod.ext hp
        apply hinj (adjacent e).2
        have he : slot p.1.1 p.1.2 = e := p.2
        rw [hp] at he
        exact he.trans hl.symm
    rw [huniv, Finset.sum_pair hab]
    exact hpair _ _ k l (hdistinct e) (hk.trans hl.symm)
  have h := (Equiv.sigmaFiberEquiv f).sum_comp (fun p : I × Fin 3 => term p.1 p.2)
  change (∑ p : (e : E) × {p : I × Fin 3 // f p = e}, term p.2.1.1 p.2.1.2) =
    ∑ p : I × Fin 3, term p.1 p.2 at h
  simpa only [Fintype.sum_sigma, Fintype.sum_prod_type, hfiber, Finset.sum_const_zero] using h.symm

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
  [T3Space S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S] [IsManifold (𝓡 2) ∞ S]
  {I : Type*} [Fintype I]
  (face : I → SmoothFace S)
  (F : I → OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) S)
  (b : I → AffineBasis (Fin 3) ℝ (EuclideanSpace ℝ (Fin 2)))
  (hF : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i) (F i).source)
  (hFi : ∀ i, ContMDiffOn (𝓡 2) (𝓡 2) ∞ (F i).symm (F i).target)
  (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (F i).source)
  (hcarrier : ∀ i, (face i).carrier = F i '' convexHull ℝ (range (b i)))
  (hboundary : ∀ i k, ((face i).boundary k).map = F i ∘
    affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
  (hinj : ∀ i k, InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1))
  (hinter : ∀ i j, i ≠ j →
    (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
      ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
        ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
    ∃ w : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {F i (b i w)})
  (hfront : ∀ i j, i ≠ j →
    (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
  (hcover : (⋃ i, (face i).carrier) = univ)

include hF hFi hsource hcarrier hboundary hinj hinter hfront hcover

theorem sum_coordinateCover_turningIntegral_eq_zero
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g)
    (Q : ∀ i, RiemannianMetric.AlignedChartFrame g (coordinateTriangleChart (F i) (b i))) :
    (∑ i, ∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1)) = 0 := by
  let _ := Fintype.ofFinite (FaceBoundaryEdge face)
  obtain ⟨adjacent, hdistinct, hexact⟩ := Euler.exists_canonical_adjacentFaces
    face F b hsource hcarrier hboundary hinj hinter hfront hcover
  let term := fun i k => coordinateTriangleTurningIntegral D (F i) (b i) (Q i) (k + 1) ((k + 1) + 1)
  have himage (i : I) (k : Fin 3) :
      (fun t : ℝ => F i (AffineMap.lineMap (b i (k + 1)) (b i ((k + 1) + 1)) t)) '' Icc (0 : ℝ) 1 =
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 := by
    rw [coordinateTriangle_cyclic_boundary_image, hboundary, image_comp]
    congr 1
    unfold affineSegment
    apply image_congr
    intro t _
    simp only [affineChartSegment, AffineMap.lineMap_apply_module]
    module
  have hpair (i j : I) (k l : Fin 3) (hij : i ≠ j)
      (he : faceBoundaryIndex face i k = faceBoundaryIndex face j l) : term i k + term j l = 0 := by
    apply coordinateTriangleTurningIntegral_pair_eq_zero D (F i) (F j) (b i) (b j)
      (hF i) (hFi i) (hF j) (hFi j) (hsource i) (hsource j) (Q i) (Q j) (k + 1) (l + 1)
    · rw [himage, himage]
      exact (faceBoundaryIndex_eq_iff face i j k l).mp he
    · rw [← hcarrier, ← hcarrier]
      apply disjoint_iff_inter_eq_empty.mpr
      rw [← interior_inter]
      exact g.volumeMeasure.interior_eq_empty_of_null
        (measure_mono_null (hfront i j hij) ((face i).volumeMeasure_frontier_eq_zero g))
  have h := sum_slots_eq_zero_of_two_faces (faceBoundaryIndex face)
    (Euler.coordinate_faceBoundaryIndex_injective face F b hsource hboundary)
    adjacent hdistinct hexact term hpair
  have hreindex (i : I) : (∑ k : Fin 3, term i k) =
      ∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1) :=
    Equiv.sum_comp (Equiv.addRight (1 : Fin 3))
      (fun k => coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1))
  simpa only [hreindex] using h

theorem integral_scalarCurvature_eq_coordinateVertex_sum [CompactSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      2 * (∑ v : Euler.CoordinateVertex F b, coordinateVertexAngleContribution g F b v.1) -
        2 * Real.pi * Nat.card I := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  let Q := fun i => g.alignedChartFrame (coordinateTriangleChart (F i) (b i))
    (coordinateTriangleChart_smooth (F i) (b i) (hFi i))
    (coordinateTriangleChart_smooth_symm (F i) (b i) (hF i))
  have hedge := sum_coordinateCover_turningIntegral_eq_zero face F b hF hFi hsource
    hcarrier hboundary hinj hinter hfront hcover D Q
  have hdisjoint : Pairwise (fun i j => AEDisjoint g.volumeMeasure
      (face i).carrier (face j).carrier) := fun i j hij =>
    measure_mono_null (hfront i j hij) ((face i).volumeMeasure_frontier_eq_zero g)
  have hint : (∑ i, ∫ x in F i '' convexHull ℝ (range (b i)),
      D.scalarCurvature x ∂g.volumeMeasure) = ∫ x, D.scalarCurvature x ∂g.volumeMeasure := by
    have h := integral_iUnion_ae
      (fun i => (face i).isCompact_carrier.measurableSet.nullMeasurableSet)
      hdisjoint (D.integrable_scalarCurvature.integrableOn (s := ⋃ i, (face i).carrier))
    rw [hcover, Measure.restrict_univ] at h
    simpa only [tsum_fintype, hcarrier] using h.symm
  have hsum : (∑ i,
      ((∫ x in F i '' convexHull ℝ (range (b i)), D.scalarCurvature x ∂g.volumeMeasure) +
        2 * (∑ k : Fin 3, coordinateTriangleTurningIntegral D (F i) (b i) (Q i) k (k + 1)) +
        2 * (∑ k : Fin 3, (Real.pi - coordinateTriangleAngle g (F i) (b i) k)))) =
      ∑ _i : I, 4 * Real.pi :=
    Finset.sum_congr rfl (fun i _ =>
      gaussBonnet_coordinateTriangle_side_integrals D (F i) (b i) (hF i) (hFi i) (hsource i) (Q i))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul] at hsum
  rw [hint, hedge, mul_zero, add_zero] at hsum
  have hcorners : (∑ i, ∑ k : Fin 3, (Real.pi - coordinateTriangleAngle g (F i) (b i) k)) =
      3 * Real.pi * Fintype.card I - ∑ i, ∑ k : Fin 3, coordinateTriangleAngle g (F i) (b i) k := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcorners] at hsum
  rw [sum_coordinateVertexAngleContribution, Nat.card_eq_fintype_card]
  linarith

theorem integral_scalarCurvature_eq_euler_add_vertex_excess [CompactSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) =
      4 * Real.pi * ((Nat.card (Euler.CoordinateVertex F b) : ℝ) -
        Nat.card (FaceBoundaryEdge face) + Nat.card I) +
      2 * (∑ v : Euler.CoordinateVertex F b,
        (coordinateVertexAngleContribution g F b v.1 - 2 * Real.pi)) := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  have hi := integral_scalarCurvature_eq_coordinateVertex_sum face F b hF hFi hsource
    hcarrier hboundary hinj hinter hfront hcover D
  have hc : (3 : ℝ) * Nat.card I = 2 * Nat.card (FaceBoundaryEdge face) := by
    exact_mod_cast three_card_coordinate_faces_eq_two_card_boundary_edges
      face F b hsource hcarrier hboundary hinj hinter hfront hcover
  rw [hi, Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  nlinarith [congrArg (fun x : ℝ => Real.pi * x) hc]

theorem integral_scalarCurvature_le_eight_pi_add_vertex_excess
    [CompactSpace S] [ConnectedSpace S]
    {g : RiemannianMetric 2 S} (D : LeviCivitaData g) :
    letI := Fintype.ofFinite (Euler.CoordinateVertex F b)
    (∫ x, D.scalarCurvature x ∂g.volumeMeasure) ≤ 8 * Real.pi +
      2 * (∑ v : Euler.CoordinateVertex F b,
        (coordinateVertexAngleContribution g F b v.1 - 2 * Real.pi)) := by
  let _ := Fintype.ofFinite (Euler.CoordinateVertex F b)
  rw [integral_scalarCurvature_eq_euler_add_vertex_excess face F b hF hFi hsource
    hcarrier hboundary hinj hinter hfront hcover D]
  have hχ : (Nat.card (Euler.CoordinateVertex F b) : ℝ) -
      Nat.card (FaceBoundaryEdge face) + Nat.card I ≤ 2 := by
    exact_mod_cast Euler.eulerCount_le_two_of_coordinate_cover
      face F b hsource hcarrier hboundary hinj hinter hfront hcover
  have hscaled := mul_le_mul_of_nonneg_left hχ (show 0 ≤ 4 * Real.pi by positivity)
  nlinarith

end PoincareConjecture.Topology.Surface
