import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEuler
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerCapped
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegionDiskEulerTopology












noncomputable section
set_option autoImplicit false

open Set
open scoped Topology ContDiff Manifold
open PoincareConjecture.Topology.Surface

namespace PoincareConjecture





theorem m64Intrinsic_region_euler_ge_one_of_coordinate_triangulation
    {I : Type*} [Finite I] [Nonempty I]
    (face : I → SmoothFace AnnulusCoordinates)
    (C : I → OpenPartialHomeomorph AnnulusCoordinates AnnulusCoordinates)
    (b : I → AffineBasis (Fin 3) ℝ AnnulusCoordinates)
    (hsource : ∀ i, convexHull ℝ (range (b i)) ⊆ (C i).source)
    (hcarrier : ∀ i, (face i).carrier = C i '' convexHull ℝ (range (b i)))
    (hboundary : ∀ i k, ((face i).boundary k).map = C i ∘
      affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)))
    (hfront : ∀ i j, i ≠ j →
      (face i).carrier ∩ (face j).carrier ⊆ frontier (face i).carrier)
    (hinter : ∀ i j, i ≠ j →
      (∃ k l : Fin 3, (face i).carrier ∩ (face j).carrier =
          ((face i).boundary k).map '' Icc (0 : ℝ) 1 ∧
        ((face i).boundary k).map '' Icc (0 : ℝ) 1 =
          ((face j).boundary l).map '' Icc (0 : ℝ) 1) ∨
      ∃ v : Fin 3, (face i).carrier ∩ (face j).carrier ⊆ {C i (b i v)})
    {U V : Set AnnulusCoordinates} (hU : IsOpen U) (hV : IsOpen V)
    (hdisj : Disjoint U V) (hfrontier : frontier U = frontier V)
    (hclosure : closure U ∪ closure V = univ)
    (hregion : (⋃ i, (face i).carrier) = closure U) (hVconn : IsPreconnected V) :
    (1 : ℤ) ≤ (Nat.card (Euler.CoordinateVertex C b) : ℤ) -
      Nat.card (FaceBoundaryEdge face) + Nat.card I := by
  classical
  let _ := Fintype.ofFinite I
  let _ := Fintype.ofFinite (Euler.CoordinateVertex C b)
  let _ := Fintype.ofFinite (FaceBoundaryEdge face)
  let _ : Nonempty (Euler.CoordinateVertex C b) :=
    ⟨Euler.coordinateCorner C b (Classical.arbitrary I) 0⟩
  let ends := Euler.coordinateEdgeEnds face C b
  let edge := fun e : FaceBoundaryEdge face => (faceBoundaryEdge face e).map
  have hinjslot (i : I) (k : Fin 3) :
      InjOn ((face i).boundary k).map (Icc (0 : ℝ) 1) := by
    have hne : b i (k.succAbove 1) - b i (k.succAbove 0) ≠ 0 := by
      apply sub_ne_zero.mpr
      intro heq
      have h := Fin.succAbove_right_injective (p := k) ((b i).ind.injective heq)
      norm_num at h
    have hseg {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
        affineChartSegment (b i (k.succAbove 0)) (b i (k.succAbove 1)) t ∈ (C i).source :=
      hsource i (Euler.coordinate_edge_subset_hull (b i) k
        (Euler.affineChartSegment_image _ _ ▸ mem_image_of_mem _ ht))
    intro t ht s hs heq
    rw [hboundary] at heq
    exact smul_left_injective ℝ hne (add_left_cancel ((C i).injOn (hseg ht) (hseg hs) heq))
  have hcont (e : FaceBoundaryEdge face) : ContinuousOn (edge e) (Icc 0 1) :=
    (faceBoundaryEdge face e).smooth.continuousOn
  have hinj (e : FaceBoundaryEdge face) : InjOn (edge e) (Icc 0 1) :=
    hinjslot e.out.1 e.out.2
  have hstart (e : FaceBoundaryEdge face) :
      edge e 0 = ((ends e).1 : AnnulusCoordinates) := by
    dsimp only [edge, ends, Euler.coordinateEdgeEnds, Euler.coordinateCorner, faceBoundaryEdge]
    rw [hboundary]
    simp [affineChartSegment]
  have hend (e : FaceBoundaryEdge face) :
      edge e 1 = ((ends e).2 : AnnulusCoordinates) := by
    dsimp only [edge, ends, Euler.coordinateEdgeEnds, Euler.coordinateCorner, faceBoundaryEdge]
    rw [hboundary]
    simp [affineChartSegment]
  have hmeet (e d : FaceBoundaryEdge face) (hed : e ≠ d) :
      edge e '' Icc 0 1 ∩ edge d '' Icc 0 1 ⊆ {edge e 0, edge e 1} := by
    apply Euler.coordinate_cover_edge_meet face C b hsource hboundary hinjslot hinter
      e.out.1 d.out.1 e.out.2 d.out.2
    intro heq
    apply hed
    have h := (faceBoundaryIndex_eq_iff face e.out.1 d.out.1 e.out.2 d.out.2).mpr heq
    exact (Quotient.out_eq e).symm.trans (h.trans (Quotient.out_eq d))
  obtain ⟨hclosed, hregular, _, hcover, _⟩ :=
    m64Intrinsic_capped_region_cover face C b hsource hcarrier hfront hU hV hdisj
      hfrontier hclosure hregion
  obtain ⟨adjacent, _, hinc⟩ := m64Intrinsic_exists_capped_region_adjacent_faces
    face C b hsource hcarrier hboundary hfront hinter hU hV hdisj hfrontier hclosure hregion
  have hinteriors := m64Intrinsic_capped_region_interiors face C b hsource hcarrier hfront
    hU hV hdisj hfrontier hregion hVconn
  have hfill := m64Intrinsic_plane_graph_cycle_fill ends
    (fun v : Euler.CoordinateVertex C b => (v : AnnulusCoordinates)) Subtype.val_injective
    edge hcont hinj hstart hend hmeet (m64Intrinsic_cappedRegionCarrier face V)
    hclosed hregular (fun a => (hinteriors a).1) hcover (fun a => (hinteriors a).2) adjacent hinc
  simpa only [Nat.card_eq_fintype_card] using
    m64Intrinsic_region_euler_ge_one_of_capped_cycle_fill ends adjacent hfill

end PoincareConjecture
