import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSide
import PoincareConjecture.Proofs.M28.Mathlib.LastClosedVisit










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M28.SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}





theorem exists_final_initial_graph_subarc (T : SourceTubeData S)
    (f : UnitTwoSphere → ℝ) (hf : Continuous f)
    (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    {gamma : ℝ → (E.flow.slice E.time).carrier} {a b : ℝ} (hab : a ≤ b)
    (hgamma : ContinuousOn gamma (Icc a b))
    (hT : MapsTo gamma (Icc a b) (T.carrierOpen : Set _))
    (ha : gamma a ∈ range (fun q => (T.list.node 0).2.coordinate_map (q, f q)))
    (hb : gamma b ∉ (T.list.node 0).2.belowGraph_m28 f) :
    ∃ t ∈ Icc a b,
      gamma t ∈ range (fun q => (T.list.node 0).2.coordinate_map (q, f q)) ∧
      MapsTo gamma (Icc t b) ((T.list.node 0).2.belowGraph_m28 f)ᶜ := by
  let N := (T.list.node 0).2
  have hneck : T.tube.chain.neck 0 = N := congrFun T.tube_chain_readout.2 0
  have heps : N.epsilon = epsilon := by
    rw [← hneck, T.tube.chain.epsilon_eq 0 T.isLeast_tube_chain_zero.1, T.epsilon_eq]
  have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
  have hdom (q : UnitTwoSphere) : f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    rw [heps]
    have hh := abs_lt.mp (hbound q)
    constructor <;> linarith [hh.1, hh.2, inv_pos.mpr hepspos]
  have hmap : Continuous (fun q : UnitTwoSphere => N.coordinate_map (q, f q)) := by
    rw [← continuousOn_univ]
    exact N.coordinate_map_smooth.continuousOn.comp
      (continuous_id.prodMk hf).continuousOn (fun q _ => ⟨mem_univ _, hdom q⟩)
  have hclosed : IsClosed (range (fun q : UnitTwoSphere => N.coordinate_map (q, f q))) :=
    (isCompact_range hmap).isClosed
  obtain ⟨t, ht, htS, hafter⟩ :=
    Poincare.exists_last_visit_component hclosed hab hgamma hT ha
  refine ⟨t, ht, htS, ?_⟩
  intro v hv hvneg
  rcases eq_or_lt_of_le hv.1 with heq | hlt
  · subst v
    exact (ne_of_lt hvneg.2) ((N.mem_coordinate_graph_iff_m28 f hdom).mp htS).2
  · have hcomp := hafter v ⟨hlt, hv.2⟩
    have hend : gamma b ∈ connectedComponentIn
        ((T.carrierOpen : Set _) \
          range (fun q : UnitTwoSphere => N.coordinate_map (q, f q))) (gamma b) :=
      mem_connectedComponentIn (connectedComponentIn_nonempty_iff.mp ⟨gamma v, hcomp⟩)
    rw [connectedComponentIn_eq hcomp] at hend
    have hnegative := (T.initial_graph_negative_region f hf hbound).2.2 (gamma v) hvneg
    change gamma b ∈ connectedComponentIn
      (T.tube.carrier \ range (fun q => (T.list.node 0).2.coordinate_map (q, f q)))
        (gamma v) at hend
    rw [hnegative] at hend
    exact hb hend

end PoincareConjecture.M28.SourceTubeData
