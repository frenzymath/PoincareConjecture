import PoincareConjecture.Proofs.M28.Mathlib.ExitPrefixRemainder
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeEndTails
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceInitialGraphSide
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckSlabRegularity

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal Bundle

universe u

namespace PoincareConjecture.M28.SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}

theorem short_path_mapsTo_of_terminal_avoidance (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 1000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    {gamma : ℝ → (E.flow.slice E.time).carrier}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 gamma (Icc (0 : ℝ) 1))
    (h0 : gamma 0 ∈ (T.carrierOpen : Set _))
    (hside : gamma 0 ∉ (T.list.node 0).2.belowGraph_m28 f)
    (havoid : ∀ t ∈ Icc (0 : ℝ) 1, gamma t ∉
      closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier))
    (hshort : (E.flow.metric E.time).pathELength gamma 0 1 <
      ENNReal.ofReal (((T.list.node 0).2.scale * Real.sqrt (1 - epsilon)) *
        (27 * epsilon⁻¹ / 32))) :
    MapsTo gamma (Icc (0 : ℝ) 1) (T.carrierOpen : Set _) := by
  let N := (T.list.node 0).2
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have heps : N.epsilon = epsilon := T.list.node_epsilon (by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega)
  have hepspos : 0 < epsilon := heps ▸ N.epsilon_pos
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr hepspos
  obtain ⟨hK, hKV⟩ := T.coreUnion_compact_subset (by norm_num : (7 / 8 : ℝ) < 1)
  have hcover : (T.carrierOpen : Set _) ⊆ T.coreUnion (7 / 8) ∪
      N.region (-epsilon⁻¹) (-((7 / 8 : ℝ) * epsilon⁻¹)) ∪
        closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier) := by
    intro x hx
    rcases T.subset_coreUnion_end_tails hsmall (by norm_num : (3 / 4 : ℝ) ≤ 7 / 8)
        hx with (hk | hf') | hl
    · exact Or.inl (Or.inl hk)
    · exact Or.inl (Or.inr hf')
    · exact Or.inr (subset_closure hl.1)
  by_contra hexit
  obtain ⟨s, hs, htail, hprefix⟩ :=
    hgamma.continuousOn.exists_prefix_in_remainder_of_exit
      (F := N.region (-epsilon⁻¹) (-((7 / 8 : ℝ) * epsilon⁻¹))) T.carrierOpen.isOpen
      hK.isClosed hKV isClosed_closure hcover
      h0 havoid hexit
  · have hsF : gamma s ∈ N.belowGraph_m28 f := by
      refine ⟨htail.1, ?_⟩
      have hb := (abs_lt.mp (hbound (N.coordinate_inverse (gamma s)).1)).1
      linarith only [htail.2.2, hb, hA]
    have hconn := isPreconnected_Icc.image gamma
      (hgamma.continuousOn.mono (Icc_subset_Icc le_rfl hs.2))
    obtain ⟨y, ⟨t, ht, rfl⟩, hfront⟩ := hconn.exists_mem_frontier_of_mem_of_notMem
      ⟨s, right_mem_Icc.mpr hs.1, rfl⟩ hsF ⟨0, left_mem_Icc.mpr hs.1, rfl⟩ hside
    have hgraph : gamma t ∈ range (fun q => N.coordinate_map (q, f q)) :=
      (T.initial_graph_negative_region f hf hbound).2.1 ▸ ⟨hfront, hprefix ht⟩
    obtain ⟨q, hq⟩ := hgraph
    have hdom : f q ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
      rw [heps]
      have hb := abs_lt.mp (hbound q)
      constructor <;> linarith [hb.1, hb.2]
    have htN : gamma t ∈ N.carrier :=
      hq ▸ N.coordinate_map_mem_of_axial (q, f q) hdom
    have htheight : (N.coordinate_inverse (gamma t)).2 = f q := by
      rw [← hq, N.coordinate_inverse_coordinate_map_of_axial (q, f q) hdom]
    have hmargin : 27 * epsilon⁻¹ / 32 <
        N.epsilon⁻¹ - |(N.coordinate_inverse (gamma t)).2| := by
      rw [heps, htheight]
      linarith [hbound q]
    have hnot : gamma s ∉ N.region
        ((N.coordinate_inverse (gamma t)).2 - 27 * epsilon⁻¹ / 32)
        ((N.coordinate_inverse (gamma t)).2 + 27 * epsilon⁻¹ / 32) := by
      intro hh
      rw [htheight] at hh
      have hb := (abs_lt.mp (hbound q)).1
      linarith only [hh.2.1, htail.2.2, hb]
    have hfar : ENNReal.ofReal ((N.scale * Real.sqrt (1 - N.epsilon)) *
        (27 * epsilon⁻¹ / 32)) ≤
          (E.flow.metric E.time).edist (gamma t) (gamma s) := by
      apply le_of_not_gt
      intro hnear
      exact hnot (N.ball_subset_centered_region htN (by positivity) hmargin hnear)
    let : Bundle.RiemannianBundle
        (TangentSpace (𝓡 3) : (E.flow.slice E.time).carrier → Type _) :=
      ⟨(E.flow.metric E.time).toRiemannianMetric⟩
    have hlength : (E.flow.metric E.time).edist (gamma t) (gamma s) ≤
        (E.flow.metric E.time).pathELength gamma 0 1 :=
      (Manifold.riemannianEDist_le_pathELength
        (hgamma.mono (Icc_subset_Icc ht.1 hs.2)) rfl rfl ht.2).trans
          (Manifold.pathELength_mono ht.1 hs.2)
    rw [heps] at hfar
    exact (not_lt_of_ge (hfar.trans hlength)) hshort

end PoincareConjecture.M28.SourceTubeData
