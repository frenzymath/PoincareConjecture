import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceFiniteWalk
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallRetainedPath











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}



theorem source_neck_subset_tube_carrier
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {k : ℕ} {i : ℤ}
    (hi : i ∈ (T k).chain.shape.active) :
    ((T k).chain.neck i).carrier ⊆ (T k).carrierOpen := by
  intro x hx
  change x ∈ (T k).tube.carrier
  rw [(T k).carrier_eq]
  change x ∈ ⋃ j : {j // j ∈ (T k).chain.shape.active},
    ((T k).chain.neck j.1).carrier
  exact mem_iUnion.mpr ⟨⟨i, hi⟩, hx⟩




theorem source_connector_base_subarc
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) {k : ℕ} {i : ℤ}
    (hi : i ∈ (T k).chain.shape.active) {v : ℝ}
    (hlocal : MapsTo (H.segment k).path
      (Icc (min v ((T k).list.node i).1) (max v ((T k).list.node i).1))
      ((T k).chain.neck i).carrier) :
    MapsTo (H.segment k).path
      (Icc (min (H.segment k).lower v) (max (H.segment k).lower v))
      (T k).carrierOpen := by
  have hiL : i ∈ (T k).list.active := by
    rw [(T k).shape_eq] at hi
    exact hi
  have ht := (T k).list.node_time_mem hiL
  intro t ht'
  have hcover :
      uIcc (H.segment k).lower v ⊆
        uIcc (H.segment k).lower ((T k).list.node i).1 ∪
          uIcc ((T k).list.node i).1 v := uIcc_subset_uIcc_union_uIcc
  rcases hcover ht' with hleft | hright
  · rw [uIcc_of_le ht.1] at hleft
    exact (T k).path_mem ⟨hleft.1, hleft.2.trans ht.2⟩
  · apply source_neck_subset_tube_carrier H T hi
    apply hlocal
    change t ∈ Icc (min ((T k).list.node i).1 v)
      (max ((T k).list.node i).1 v) at hright
    simpa only [min_comm, max_comm] using hright

private theorem connector_factor_le_eight (hepsilon : epsilon ≤ (1 / 1000 : ℝ)) :
    Real.sqrt (1 + epsilon) * Real.sqrt 2 * (Real.pi + 1) ≤ (8 : ℝ) := by
  have hroot : Real.sqrt (1 + epsilon) ≤ (101 / 100 : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by linarith⟩
  have htwo : Real.sqrt 2 ≤ (3 / 2 : ℝ) :=
    (Real.sqrt_le_iff).mpr ⟨by norm_num, by norm_num⟩
  have hproduct := mul_le_mul hroot htwo (Real.sqrt_nonneg 2) (by norm_num)
  have hpi : Real.pi + 1 ≤ (5 : ℝ) := by linarith [Real.pi_le_four]
  have hbound := mul_le_mul hproduct hpi (by positivity) (by norm_num)
  exact hbound.trans (by norm_num)




theorem normalized_source_connector_of_finite_walk
    (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ)
    (W : SourceFiniteWalk H T k) (hepsilon : epsilon ≤ (1 / 1000 : ℝ))
    {i : ℤ} (hi : i ∈ (T k).chain.shape.active)
    (x : (T k).carrierOpen)
    (hx : x.val ∈ ((T k).chain.neck i).carrier) :
    ∃ v ∈ Icc (0 : ℝ) 1, ∃ hv : (H.segment k).path v ∈ (T k).carrierOpen,
      MapsTo (H.segment k).path
        (Icc (min (H.segment k).lower v) (max (H.segment k).lower v))
        (T k).carrierOpen ∧
      (H.tubeMetric T k).edist x ⟨(H.segment k).path v, hv⟩ ≤
        ENNReal.ofReal (8 * H.tubeNodeScale T k i) := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let g := (E (k + H.shift)).flow.metric (E (k + H.shift)).time
  let N := (T k).chain.neck i
  have hnode : N = ((T k).list.node i).2 := by
    dsimp only [N]
    rw [(T k).neck_eq]
    exact (T k).list.neckOfList_eq_node i
  obtain ⟨v, hv, hvN, _hlevel, c, _hc, d, _hd, _hvcd, _hpathcd,
    hlocal, hdist⟩ := W.connector i hi x.val hx
  have hvT := source_neck_subset_tube_carrier H T hi hvN
  let y : (T k).carrierOpen := ⟨(H.segment k).path v, hvT⟩
  have hexact : (H.tubeMetric T k).edist x y ≤
      ENNReal.ofReal (H.tubeNodeScale T k i * Real.sqrt (1 + epsilon) *
        Real.sqrt 2 * (Real.pi + 1)) := by
    calc
      _ ≤ intrinsicEDist (H.normalizedSliceMetric k) N.carrier x.val y.val := by
        rw [tubeMetric, intrinsicOpenMetric_edist]
        exact intrinsicEDist_mono_of_subset (g := H.normalizedSliceMetric k)
          (source_neck_subset_tube_carrier H T hi)
      _ = ENNReal.ofReal (Real.sqrt Q) * intrinsicEDist g N.carrier x.val y.val :=
        H.normalizedSlice_intrinsicEDist k N.carrier x.val y.val
      _ ≤ ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal
          (N.scale * Real.sqrt (1 + epsilon) * Real.sqrt 2 * (Real.pi + 1)) :=
        by simpa only [mul_comm] using
          (mul_le_mul_left hdist (ENNReal.ofReal (Real.sqrt Q)))
      _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
        congr 1
        dsimp only [tubeNodeScale, Q, N] at hnode ⊢
        rw [hnode]
        ring
  have hcost : H.tubeNodeScale T k i * Real.sqrt (1 + epsilon) *
      Real.sqrt 2 * (Real.pi + 1) ≤ 8 * H.tubeNodeScale T k i := by
    have h := mul_le_mul_of_nonneg_left (connector_factor_le_eight hepsilon)
      (H.tubeNodeScale_pos T k i).le
    nlinarith only [h]
  refine ⟨v, hv, hvT, source_connector_base_subarc H T hi hlocal, ?_⟩
  exact hexact.trans (ENNReal.ofReal_le_ofReal hcost)

end PoincareConjecture.M28.CounterexampleNeckFamily
