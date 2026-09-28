import PoincareConjecture.Proofs.M76.Horizon.Dehn.Circles.Tubes.LocalBranchTargetComplex
import PoincareConjecture.Proofs.M76.Horizon.Dehn.DoubleArc.OriginalVertexCoordinateSectors
import PoincareConjecture.Proofs.M76.Wall.OriginalInteriorEdgeDual
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.MaximalFaceDual
import PoincareConjecture.Proofs.M76.Rigidity.Mathlib.EmbeddedFaceDimension
import PoincareConjecture.Proofs.M76.Mathlib.BarycentricDualSubcomplex

set_option autoImplicit false
open Set Metric Geometry Topology

namespace PoincareConjecture.M76.Dehn

local notation "V2" => (Fin 2 → ℝ)
local notation "V3" => (Fin 3 → ℝ)

open Classical in

theorem ComponentBranchModel.exists_raw_edge_joint
    {X ι : Type*} [TopologicalSpace X]
    {e : ι → OpenPartialHomeomorph X V3} {f : V2 → X} {R : Set X}
    {old : OrdinaryDoubleCurveModel e f R} {i : old.Index}
    (D : ComponentBranchModel old i)
    (s : Finset (D.sample → ℝ × V3)) (hs : s ∈ D.axis.faces) (hcard : s.card = 2)
    (p : D.sample → ℝ × V3) (hps : p ∈ s) :
    letI : Fintype D.complex.faces := D.complex_finite.fintype
    ∃ (x y : V2) (C : RawCrossingChart e f R x y),
      MapsTo (fun z ↦ (D.inverse z : X)) (D.complex.closedStar p).space C.chart.source ∧
      (D.complex.closedStar p).AffineOnFaces (fun z ↦ C.chart (D.inverse z)) ∧
      (∀ z ∈ (D.complex.closedStar p).space,
        z ∈ D.axis.space ↔ (D.inverse z : X) ∈ R ∧
          C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0) ∧
      (∀ j : Fin 2,
        ((D.complex.closedStar p).vertexSubcomplex
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}).space =
        (D.complex.closedStar p).space ∩
          {z | (D.inverse z : X) ∈ R ∧ C.chart (D.inverse z) j.castSucc = 0}) ∧
      IsFinitePLBallPair (ℝ × ℝ) (D.complex.barycentricDualBlock s).space
        ((D.complex.barycentricDualBlock s).link (s.centroid ℝ id)).space ∧
      (D.complex.barycentricDualBlock s).space ∩ D.axis.space = {s.centroid ℝ id} := by
  classical
  let : Fintype D.complex.faces := D.complex_finite.fintype
  have hp := D.axis.face_subset_vertices hs hps
  obtain ⟨x, y, C, hC, hface, haxis, hsheet⟩ := D.exists_marked_raw_star p hp
  have hpcore : (D.inverse p : X) ∈ interior D.core := by
    apply D.core_neighborhood
    obtain ⟨a, ha, hap⟩ := D.axis_space.subset (D.axis.vertices_subset_space hp)
    refine ⟨a, ha, ?_⟩
    exact (D.graph_separates _ (D.inverse p).property _
      ((D.graph_inverse p (D.complex.vertices_subset_space (D.axis_le hp))).trans hap.symm)).symm
  have hsubstar : D.axis.closedStar p ≤ D.complex.closedStar p :=
    fun _ ht => ⟨D.axis_le ht.1, D.axis_le ht.2⟩
  have hstarzero (z : D.sample → ℝ × V3) (hz : z ∈ (D.axis.closedStar p).space) :
      C.chart (D.inverse z) 0 = 0 ∧ C.chart (D.inverse z) 1 = 0 :=
    ((haxis z (SimplicialComplex.space_subset_of_le hsubstar hz)).mp
      (SimplicialComplex.space_subset_of_le (show D.axis.closedStar p ≤ D.axis
        from fun _ ht => ht.1) hz)).2
  have hstarinj := (D.complex.exists_original_open_neighborhood_inside_closedStar
    D.complex_finite D.homeomorph D.inverse D.inverse_value (D.axis_le hp) hpcore C.chart hC).1
  have hheight : (D.axis.closedStar p).AffineOnFaces (fun z => C.chart (D.inverse z) 2) := by
    change (D.axis.closedStar p).AffineOnFaces
      (((ContinuousLinearMap.proj (2 : Fin 3) : V3 →L[ℝ] ℝ).toContinuousAffineMap) ∘
        fun z => C.chart (D.inverse z))
    exact (show (D.axis.closedStar p).AffineOnFaces (fun z => C.chart (D.inverse z)) from
      fun t ht => hface t (hsubstar ht)).postcomp _
  have hheightinj : InjOn (fun z => C.chart (D.inverse z) 2) (D.axis.closedStar p).space := by
    intro z hz w hw he
    apply hstarinj (SimplicialComplex.space_subset_of_le hsubstar hz)
      (SimplicialComplex.space_subset_of_le hsubstar hw)
    ext j
    fin_cases j
    · exact (hstarzero z hz).1.trans (hstarzero w hw).1.symm
    · exact (hstarzero z hz).2.trans (hstarzero w hw).2.symm
    · exact he
  have hmax (t : Finset (D.sample → ℝ × V3)) (ht : t ∈ D.axis.faces) (hst : s ⊆ t) : t = s := by
    have htstar : t ∈ (D.axis.closedStar p).faces :=
      ⟨ht, by simpa only [Finset.insert_eq_of_mem (hst hps)] using ht⟩
    have hbound := hheight.face_card_le_of_injOn hheightinj htstar
    exact (Finset.eq_of_subset_of_card_le hst (by simpa [hcard] using hbound)).symm
  let : Fintype D.axis.faces := (D.complex_finite.subset D.axis_le).fintype
  refine ⟨x, y, C, hC, hface, haxis, hsheet,
    isFinitePLBallPair_original_interior_edge_dual D.complex D.homeomorph D.inverse
      D.inverse_value (D.axis_le hs) hcard hps hpcore C.chart hC hface, ?_⟩
  exact (D.complex.barycentricDualBlock_space_inter_subcomplex D.axis D.axis_le s).trans
    (D.axis.barycentricDualBlock_space_eq_singleton_of_maximal hs hmax)

end PoincareConjecture.M76.Dehn
