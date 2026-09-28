import PoincareConjecture.Proofs.M28.Sec10_3_Tube.NeckMinimizerSameLevel
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeData
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceNeckRegion















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28

open PoincareConjecture.EpsilonNeck

theorem exists_source_neck_path_connector_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A D₀ D : ℝ}
        {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
        (S : CounterexampleNeckSegment E),
        0 < E.flow.scalar ⟨E.time, E.basepoint⟩ → epsilon ≤ epsilon₀ →
        ∀ T : SourceTubeData S,
        ∀ i : ℤ, i ∈ T.chain.shape.active →
        ∀ x : (E.flow.slice E.time).carrier,
          x ∈ (T.chain.neck i).carrier →
          ∃ v ∈ Icc (0 : ℝ) 1,
            S.path v ∈ (T.chain.neck i).carrier ∧
            ((T.chain.neck i).coordinate_inverse (S.path v)).2 =
              ((T.chain.neck i).coordinate_inverse x).2 ∧
            ∃ c ∈ Ioo (0 : ℝ) 1, ∃ d ∈ Ioo (0 : ℝ) 1,
              v ∈ Icc c d ∧
              MapsTo S.path (Icc c d) (T.chain.neck i).carrier ∧
              MapsTo S.path (Icc (min v ((T.list.node i).1))
                (max v ((T.list.node i).1))) (T.chain.neck i).carrier ∧
            intrinsicEDist (E.flow.metric E.time)
              (T.chain.neck i).carrier x (S.path v) ≤
              ENNReal.ofReal ((T.chain.neck i).scale *
                Real.sqrt (1 + epsilon) * Real.sqrt 2 * (Real.pi + 1)) := by
  obtain ⟨epsilonR, hRpos, hRsmall, hregion⟩ :=
    exists_source_neck_region_accuracy.{u}
  obtain ⟨epsilonE, hEpos, hEsmall, hend⟩ :=
    exists_source_neck_endpoint_exclusion_accuracy.{u}
  refine ⟨min (1 / 1000 : ℝ) (min epsilonR epsilonE),
    lt_min (by norm_num) (lt_min hRpos hEpos),
    min_le_left _ _, ?_⟩
  intro epsilon C A D₀ D E S hQ hsmall T i hi x hx
  have hsmall₁ : epsilon ≤ (1 / 1000 : ℝ) :=
    hsmall.trans (min_le_left _ _)
  have hsmallR : epsilon ≤ epsilonR :=
    hsmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallE : epsilon ≤ epsilonE :=
    hsmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hiL : i ∈ T.list.active := by
    rw [T.shape_eq] at hi
    change 0 ≤ i ∧ i ≤ (T.list.nodes.length : ℤ) - 1 at hi ⊢
    exact hi
  have hWnode : T.chain.neck i = (T.list.node i).2 := by
    rw [T.neck_eq]
    exact T.list.neckOfList_eq_node i
  obtain ⟨N, hN, hchoice, hcenter⟩ := T.list.node_provenance hiL
  have hWsubsetN : (T.chain.neck i).carrier ⊆ N.carrier := by
    rw [hWnode]
    rcases hchoice with hchoice | hchoice
    · intro y hy
      simpa only [hchoice] using hy
    · intro y hy
      simpa only [hchoice, reversed_carrier] using hy
  have hWregion : (T.chain.neck i).carrier ⊆ S.source_region.carrier := by
    have hU := (hregion E S hQ hsmallR).2.1
    exact fun y hy => hU ⟨N, hN, hWsubsetN hy⟩
  have hWunion : (T.chain.neck i).carrier ⊆ S.neckCarrierUnion := by
    intro y hy
    exact ⟨N, hN, hWsubsetN hy⟩
  have hε : (T.chain.neck i).epsilon ≤ (1 / 1000 : ℝ) := by
    rw [T.chain.epsilon_eq i hi]
    exact hsmall₁
  have htime := T.list.node_time_mem hiL
  have ht0 : (0 : ℝ) < (T.list.node i).1 :=
    S.lower_pos.trans_le htime.1
  have ht1 : (T.list.node i).1 < 1 :=
    htime.2.trans_lt S.upper_lt_one
  have hcenter' : S.path (T.list.node i).1 = (T.chain.neck i).center := by
    rw [hWnode]
    exact T.list.node_center hiL
  have h0out : S.path 0 ∉ (T.chain.neck i).carrier := by
    intro hmem
    exact (hend E S hQ hsmallE).1 (hWunion hmem)
  have h1out : S.path 1 ∉ (T.chain.neck i).carrier := by
    intro hmem
    exact (hend E S hQ hsmallE).2 (hWunion hmem)
  obtain ⟨c, hc, d, hd, v, hv, hpathW, hlocal, hlevel, hdist⟩ :=
    exists_neck_minimizer_same_level (T.chain.neck i) hε hWregion
      ht0 ht1 S.path_smooth S.source_region.path_mem
      S.source_region.minimizing hcenter' h0out h1out hx
  refine ⟨v, ⟨?_, ?_⟩, hpathW hv, hlevel, ?_⟩
  · exact (lt_of_lt_of_le hc.1 hv.1).le
  · exact (le_trans hv.2 hd.2.le)
  · refine ⟨c, ⟨hc.1, hc.2.trans ht1⟩, d, ⟨ht0.trans hd.1, hd.2⟩, ?_⟩
    refine ⟨hv, hpathW, hlocal, ?_⟩
    simpa only [T.chain.epsilon_eq i hi] using hdist

end PoincareConjecture.M28
