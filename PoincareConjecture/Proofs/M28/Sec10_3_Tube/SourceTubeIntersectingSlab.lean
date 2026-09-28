import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeFreshSlab
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeInitialPair
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicDistanceEnergy
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallRetainedPath

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M28

namespace SourceTubeData

variable {epsilon C A D0 D : ℝ}
  {E : SameTimeCounterexample.{u} epsilon C A D0 D}
  {S : CounterexampleNeckSegment E}

theorem intrinsicEDist_lt_of_initial_graph_intersection (T : SourceTubeData S)
    (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck (E.flow.metric E.time)) (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * (T.list.node 0).2.scale)
    (hterminal : Disjoint N.carrier
      (closure ((T.list.node ((T.list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    (hmeet : (range (fun q => (T.list.node 0).2.coordinate_map (q, f q)) ∩
      N.central_sphere).Nonempty)
    {x : (E.flow.slice E.time).carrier} (hx : x ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x).2| ≤ 3 * epsilon⁻¹ / 4) :
    intrinsicEDist (E.flow.metric E.time) (T.carrierOpen : Set _)
      (S.path S.lower) x < ENNReal.ofReal
        ((151 / 200 : ℝ) * ((T.list.node 0).2.scale + N.scale) * epsilon⁻¹) := by
  let N0 := (T.list.node 0).2
  have hlen : 0 < T.list.nodes.length := List.length_pos_iff.mpr T.list.nonempty
  have heps0 : N0.epsilon = epsilon := T.list.node_epsilon (by
    change 0 ≤ (0 : ℤ) ∧ (0 : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
    constructor <;> omega)
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ N.epsilon_pos)
  have hNT : N0.carrier ⊆ (T.carrierOpen : Set _) := by
    intro y hy
    rw [T.carrier_eq_iUnion_nodes]
    exact mem_iUnion₂.mpr ⟨0, Finset.mem_range.mpr hlen, hy⟩
  have hdom (q : UnitTwoSphere) : f q ∈ Ioo (-N0.epsilon⁻¹) N0.epsilon⁻¹ := by
    rw [heps0]
    have hh := abs_lt.mp (hbound q)
    constructor <;> linarith [hh.1, hh.2]
  obtain ⟨y, hygraph, hycentral⟩ := hmeet
  obtain ⟨hy0, hyheight⟩ := (N0.mem_coordinate_graph_iff_m28 f hdom).mp hygraph
  have hyside : y ∉ N0.belowGraph_m28 f := by
    intro hy
    exact (ne_of_lt hy.2) hyheight
  have hyheight0 : |(N0.coordinate_inverse y).2| ≤ 3 * N0.epsilon⁻¹ / 4 := by
    rw [hyheight, heps0]
    linarith [hbound (N0.coordinate_inverse y).1]
  have hleft : intrinsicEDist (E.flow.metric E.time) (T.carrierOpen : Set _)
      (S.path S.lower) y < ENNReal.ofReal ((151 / 200 : ℝ) * N0.scale * epsilon⁻¹) := by
    rw [← T.node_zero_readout.2.2]
    have hh := (intrinsicEDist_mono_of_subset hNT).trans_lt
      (N0.intrinsicEDist_lt_three_quarter_ceiling (by rwa [heps0])
        N0.center_on_central_sphere hy0 hyheight0)
    simpa only [heps0] using hh
  obtain ⟨gamma, h0, h1, hgamma, _, hgammaT, hlength⟩ :=
    T.exists_central_slab_competitor_in_tube hsmall f hf hbound N heps hscale
      hycentral (hNT hy0) hyside hterminal hx hheight
  have hright : intrinsicEDist (E.flow.metric E.time) (T.carrierOpen : Set _) y x <
      ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * epsilon⁻¹) := by
    have hh := intrinsicEDist_le_pathELength (E.flow.metric E.time)
      zero_le_one hgamma hgammaT
    rw [h0, h1] at hh
    exact hh.trans_lt hlength
  have hxT : x ∈ (T.carrierOpen : Set _) := by
    simpa only [h1] using hgammaT (right_mem_Icc.mpr zero_le_one)
  have hscale0 := N0.scale_pos
  have hscaleN := N.scale_pos
  calc
    _ ≤ intrinsicEDist (E.flow.metric E.time) (T.carrierOpen : Set _)
        (S.path S.lower) y +
          intrinsicEDist (E.flow.metric E.time) (T.carrierOpen : Set _) y x :=
      intrinsicOpenEDist_triangle (E.flow.metric E.time) T.carrierOpen
        (T.path_mem (left_mem_Icc.mpr S.lower_lt_upper.le)) (hNT hy0) hxT
    _ < ENNReal.ofReal ((151 / 200 : ℝ) * N0.scale * epsilon⁻¹) +
        ENNReal.ofReal ((151 / 200 : ℝ) * N.scale * epsilon⁻¹) :=
      ENNReal.add_lt_add hleft hright
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      dsimp only [N0]
      ring

end SourceTubeData

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem tube_distance_lt_of_initial_graph_intersection
    (H : CounterexampleNeckFamily E) (T : ∀ k, SourceTubeData (H.segment k))
    (k : ℕ) (hsmall : epsilon ≤ (1 / 10000 : ℝ)) (f : UnitTwoSphere → ℝ)
    (hf : Continuous f) (hbound : ∀ q, |f q| < epsilon⁻¹ / 32)
    (N : EpsilonNeck ((E (k + H.shift)).flow.metric (E (k + H.shift)).time))
    (heps : N.epsilon = epsilon)
    (hscale : N.scale ≤ (101 / 100 : ℝ) * ((T k).list.node 0).2.scale)
    (hterminal : Disjoint N.carrier
      (closure (((T k).list.node (((T k).list.nodes.length - 1 : ℕ) : ℤ)).2.carrier)))
    (hmeet : (range (fun q => ((T k).list.node 0).2.coordinate_map (q, f q)) ∩
      N.central_sphere).Nonempty)
    (x : (T k).carrierOpen) (hx : x.val ∈ N.carrier)
    (hheight : |(N.coordinate_inverse x.val).2| ≤ 3 * epsilon⁻¹ / 4) :
    (H.tubeMetric T k).edist (H.tubeBase T k) x <
      ENNReal.ofReal ((13 / 8 : ℝ) * (4 * max C 2)⁻¹ * epsilon⁻¹) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let s0 : ℝ := (4 * max C 2)⁻¹
  have hQ : 0 < Q := H.base_scalar_pos k
  have hroot : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hA : 0 < epsilon⁻¹ := inv_pos.mpr (heps ▸ N.epsilon_pos)
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hs0 : 0 < s0 := by dsimp only [s0]; positivity
  have hzero : Real.sqrt Q * ((T k).list.node 0).2.scale = s0 :=
    H.normalizedSlice_low_neck_scale k _ (T k).node_zero_readout.2.2
  have hsum : Real.sqrt Q * (((T k).list.node 0).2.scale + N.scale) ≤
      (201 / 100 : ℝ) * s0 := by
    have hh := mul_le_mul_of_nonneg_left hscale hroot.le
    nlinarith only [hh, hzero]
  have hnormalized : Real.sqrt Q * ((151 / 200 : ℝ) *
      (((T k).list.node 0).2.scale + N.scale) * epsilon⁻¹) <
        (13 / 8 : ℝ) * s0 * epsilon⁻¹ := by
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 151 / 200)) hA.le
    nlinarith only [hh, mul_pos hs0 hA]
  have hraw := (T k).intrinsicEDist_lt_of_initial_graph_intersection
    hsmall f hf hbound N heps hscale hterminal hmeet hx hheight
  rw [tubeMetric, intrinsicOpenMetric_edist, H.normalizedSlice_intrinsicEDist]
  change ENNReal.ofReal (Real.sqrt Q) * _ < ENNReal.ofReal ((13 / 8 : ℝ) * s0 * _)
  apply (ENNReal.mul_right_strictMono
    (ENNReal.ofReal_pos.mpr hroot).ne' ENNReal.ofReal_ne_top hraw).trans
  dsimp only
  rw [← ENNReal.ofReal_mul hroot.le]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr hnormalized

end CounterexampleNeckFamily

end PoincareConjecture.M28
