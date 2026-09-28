import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeScaleBudget
import PoincareConjecture.Proofs.M28.Generalized.FullNeckVolume
import PoincareConjecture.Proofs.M28.Generalized.MetricVolumeCalibration

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28

theorem SourceTubeData.carrier_eq_iUnion_nodes
    {epsilon C A D₀ D : ℝ}
    {E : SameTimeCounterexample.{u} epsilon C A D₀ D}
    {S : CounterexampleNeckSegment E} (T : SourceTubeData S) :
    (T.carrierOpen : Set _) =
      ⋃ i ∈ Finset.range T.list.nodes.length, (T.list.node (i : ℤ)).2.carrier := by
  change T.tube.carrier = _
  rw [T.carrier_eq]
  change (⋃ i : {i // i ∈ T.chain.shape.active}, (T.chain.neck i.1).carrier) = _
  ext x
  constructor
  · intro hx
    obtain ⟨⟨i, hi⟩, hx⟩ := mem_iUnion.mp hx
    have hi' : i ∈ T.list.active := by
      simpa only [T.shape_eq, ChainShape.active, SourceOrientedList.active] using hi
    have hid : (i.toNat : ℤ) = i := by have := hi'.1; omega
    refine mem_iUnion.mpr ⟨i.toNat, mem_iUnion.mpr
      ⟨Finset.mem_range.mpr (T.list.toNat_lt_length hi'), ?_⟩⟩
    simpa only [T.neck_eq, T.list.neckOfList_eq_node, hid] using hx
  · intro hx
    obtain ⟨i, hx⟩ := mem_iUnion.mp hx
    obtain ⟨hi, hx⟩ := mem_iUnion.mp hx
    have hi' : i < T.list.nodes.length := Finset.mem_range.mp hi
    have hactive : (i : ℤ) ∈ T.chain.shape.active := by
      rw [T.shape_eq]
      change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ (T.list.nodes.length : ℤ) - 1
      omega
    refine mem_iUnion.mpr ⟨⟨(i : ℤ), hactive⟩, ?_⟩
    simpa only [T.neck_eq, T.list.neckOfList_eq_node] using hx

namespace CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

theorem tube_cubic_scale_sum_bound (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) :
    ∑ i ∈ Finset.range (T k).list.nodes.length, H.tubeNodeScale T k (i : ℤ) ^ 3 ≤
      ((4 * max C 2)⁻¹) ^ 2 *
        (epsilon * (A + 2 * endpointConnectorBudget epsilon C) / (0.99 : ℝ)) +
          ((4 * max C 2)⁻¹) ^ 3 := by
  let m := (T k).list.nodes.length - 1
  let smax : ℝ := (4 * max C 2)⁻¹
  have hlen : 0 < (T k).list.nodes.length := List.length_pos_iff.mpr (T k).list.nonempty
  have hlength : (T k).list.nodes.length = m + 1 := by omega
  have hactive (i : ℕ) (hi : i < (T k).list.nodes.length) :
      (i : ℤ) ∈ (T k).list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
    omega
  have hsum : (∑ i ∈ Finset.range m, H.tubeNodeScale T k (i : ℤ) ^ 3) ≤
      smax ^ 2 * ∑ i ∈ Finset.range m, H.tubeNodeScale T k (i : ℤ) := by
    calc
      _ ≤ ∑ i ∈ Finset.range m, smax ^ 2 * H.tubeNodeScale T k (i : ℤ) := by
        apply Finset.sum_le_sum
        intro i hi
        have hpos := (H.tubeNodeScale_pos T k (i : ℤ)).le
        have hscale := H.tubeNodeScale_le T k (hactive i (by
          have := Finset.mem_range.mp hi
          omega))
        have hsq := pow_le_pow_left₀ hpos hscale 2
        calc
          _ = H.tubeNodeScale T k (i : ℤ) ^ 2 * H.tubeNodeScale T k (i : ℤ) := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hsq hpos
      _ = _ := (Finset.mul_sum _ _ _).symm
  have hfirst := hsum.trans (mul_le_mul_of_nonneg_left
    (H.tube_scale_sum_bound T k).le (sq_nonneg smax))
  have hlast := pow_le_pow_left₀ (H.tubeNodeScale_pos T k (m : ℤ)).le
    (H.tubeNodeScale_le T k (hactive m (by omega))) 3
  rw [hlength, Finset.sum_range_succ]
  exact add_le_add hfirst hlast

end CounterexampleNeckFamily

theorem exists_actual_source_tube_volume_constant :
    ∃ cvol : ℝ, 0 < cvol ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ),
        (H.tubeMetric T k).volumeMeasure univ ≤
          ENNReal.ofReal (cvol * (((4 * max C 2)⁻¹) ^ 2 *
            (A + 2 * endpointConnectorBudget epsilon C) / (0.99 : ℝ) +
              ((4 * max C 2)⁻¹) ^ 3 * epsilon⁻¹)) := by
  classical
  obtain ⟨cvol, hcvol, hvol⟩ := exists_full_neck_volume_upper_constant.{u}
  refine ⟨cvol, hcvol, ?_⟩
  intro epsilon C A E H T k
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let smax : ℝ := (4 * max C 2)⁻¹
  let L : ℝ := A + 2 * endpointConnectorBudget epsilon C
  have hQ : 0 < Q := H.base_scalar_pos k
  have heps : 0 < epsilon := (H.segment k).cover_epsilon ▸ (H.segment k).cover.epsilon_pos
  have hfactor : Real.rpow Q ((3 : ℝ) / 2) = Real.sqrt Q ^ (3 : ℕ) := by
    change Q ^ ((3 : ℝ) / 2) = Real.sqrt Q ^ (3 : ℕ)
    rw [Real.rpow_div_two_eq_sqrt _ hQ.le, Real.rpow_ofNat]
  have hnode (i : ℕ) (hi : i ∈ Finset.range (T k).list.nodes.length) :
      (H.normalizedSliceMetric k).volumeMeasure ((T k).list.node (i : ℤ)).2.carrier ≤
        ENNReal.ofReal (cvol * H.tubeNodeScale T k (i : ℤ) ^ 3 * epsilon⁻¹) := by
    let N := ((T k).list.node (i : ℤ)).2
    have hactive : (i : ℤ) ∈ (T k).list.active := by
      change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
      have := Finset.mem_range.mp hi
      omega
    have hN := hvol _ ((E (k + H.shift)).flow.metric (E (k + H.shift)).time) N
    rw [(T k).list.node_epsilon hactive] at hN
    have hhom := volumeMeasure_scaleSmoothMetric
      ((E (k + H.shift)).flow.metric (E (k + H.shift)).time) Q hQ N.carrier
    norm_num only [Nat.cast_ofNat] at hhom
    change (H.normalizedSliceMetric k).volumeMeasure N.carrier = _ at hhom
    rw [hhom, hfactor]
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt Q ^ (3 : ℕ)) *
          ENNReal.ofReal (cvol * N.scale ^ 3 * epsilon⁻¹) := mul_le_mul_right hN _
      _ = ENNReal.ofReal (cvol * H.tubeNodeScale T k (i : ℤ) ^ 3 * epsilon⁻¹) := by
        rw [← ENNReal.ofReal_mul (pow_nonneg (Real.sqrt_nonneg Q) 3)]
        congr 1
        dsimp only [CounterexampleNeckFamily.tubeNodeScale, N, Q]
        ring
  have hnonneg (i : ℕ) : 0 ≤ cvol * H.tubeNodeScale T k (i : ℤ) ^ 3 * epsilon⁻¹ :=
    mul_nonneg (mul_nonneg hcvol.le (pow_nonneg (H.tubeNodeScale_pos T k _).le _))
      (inv_pos.mpr heps).le
  rw [CounterexampleNeckFamily.tubeMetric, intrinsicOpenMetric_volumeMeasure_univ,
    (T k).carrier_eq_iUnion_nodes]
  calc
    _ ≤ ∑ i ∈ Finset.range (T k).list.nodes.length,
        (H.normalizedSliceMetric k).volumeMeasure ((T k).list.node (i : ℤ)).2.carrier :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ i ∈ Finset.range (T k).list.nodes.length,
        ENNReal.ofReal (cvol * H.tubeNodeScale T k (i : ℤ) ^ 3 * epsilon⁻¹) :=
      Finset.sum_le_sum hnode
    _ = ENNReal.ofReal (cvol *
        (∑ i ∈ Finset.range (T k).list.nodes.length, H.tubeNodeScale T k (i : ℤ) ^ 3) *
          epsilon⁻¹) := by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hnonneg i)]
      congr 1
      rw [← Finset.sum_mul, ← Finset.mul_sum]
    _ ≤ ENNReal.ofReal (cvol *
        (smax ^ 2 * (epsilon * L / (0.99 : ℝ)) + smax ^ 3) * epsilon⁻¹) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (H.tube_cubic_scale_sum_bound T k) hcvol.le)
        (inv_pos.mpr heps).le)
    _ = _ := by
      change ENNReal.ofReal (cvol *
        (smax ^ 2 * (epsilon * L / (0.99 : ℝ)) + smax ^ 3) * epsilon⁻¹) =
          ENNReal.ofReal (cvol * (smax ^ 2 * L / (0.99 : ℝ) + smax ^ 3 * epsilon⁻¹))
      congr 1
      field_simp [heps.ne']

theorem CounterexampleNeckFamily.exists_tube_volume_bound
    {epsilon C A : ℝ}
    {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
      ((n : ℝ) + 1) ((n : ℝ) + 1)} (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) :
    ∃ V : ℝ, 0 < V ∧ ∀ k, (H.tubeMetric T k).volumeMeasure univ ≤ ENNReal.ofReal V := by
  obtain ⟨cvol, _, h⟩ := exists_actual_source_tube_volume_constant.{u}
  let V := cvol * (((4 * max C 2)⁻¹) ^ 2 *
    (A + 2 * endpointConnectorBudget epsilon C) / (0.99 : ℝ) +
      ((4 * max C 2)⁻¹) ^ 3 * epsilon⁻¹)
  refine ⟨|V| + 1, by positivity, ?_⟩
  intro k
  exact (h H T k).trans (ENNReal.ofReal_le_ofReal
    ((le_abs_self V).trans (by linarith)))

end PoincareConjecture.M28
