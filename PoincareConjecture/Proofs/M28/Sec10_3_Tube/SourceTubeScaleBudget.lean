import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeNormalization

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology ENNReal BigOperators

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

variable {epsilon C A : ℝ}
  {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
    ((n : ℝ) + 1) ((n : ℝ) + 1)}

def tubeNodeScale (H : CounterexampleNeckFamily E)
    (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ) (i : ℤ) : ℝ :=
  Real.sqrt ((E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) *
      ((T k).list.node i).2.scale

variable (H : CounterexampleNeckFamily E)
  (T : ∀ k, SourceTubeData (H.segment k)) (k : ℕ)

theorem tubeNodeScale_pos (i : ℤ) : 0 < H.tubeNodeScale T k i :=
  mul_pos (Real.sqrt_pos.mpr (H.base_scalar_pos k)) ((T k).list.node i).2.scale_pos

theorem tubeNodeScale_le {i : ℤ} (hi : i ∈ (T k).list.active) :
    H.tubeNodeScale T k i ≤ (4 * max C 2)⁻¹ := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let N := ((T k).list.node i).2
  have hQ : 0 < Q := H.base_scalar_pos k
  have hB : 0 < max C 2 := lt_of_lt_of_le (by norm_num) (le_max_right C 2)
  have hband := ((H.segment k).scalar_band ((T k).list.node i).1
    ((T k).list.node_time_mem hi)).1
  rw [(T k).list.node_center hi] at hband
  have hscale := tube.neck_normalized_scalar_center N
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  have hsquare : (Real.sqrt Q * N.scale * (4 * max C 2)) ^ 2 ≤ 1 := by
    calc
      _ = N.scale ^ 2 * (16 * (max C 2) ^ 2 * Q) := by
        simp only [mul_pow, Real.sq_sqrt hQ.le]
        ring
      _ ≤ N.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, N.center⟩ :=
        mul_le_mul_of_nonneg_left hband (sq_nonneg _)
      _ = 1 := hscale
  have hproduct : Real.sqrt Q * N.scale * (4 * max C 2) ≤ 1 := by
    nlinarith only [hsquare, sq_nonneg (Real.sqrt Q * N.scale * (4 * max C 2) - 1)]
  change Real.sqrt Q * N.scale ≤ (4 * max C 2)⁻¹
  rw [inv_eq_one_div]
  exact (le_div_iff₀ (by positivity : 0 < 4 * max C 2)).mpr hproduct

theorem tube_edge_scale_cost_le {i : ℤ} (hi : i ∈ (T k).list.active)
    (hnext : i + 1 ∈ (T k).list.active) :
    ENNReal.ofReal ((0.99 : ℝ) * H.tubeNodeScale T k i * epsilon⁻¹) ≤
      (H.normalizedSliceMetric k).pathELength (H.segment k).path
        ((T k).list.node i).1 ((T k).list.node (i + 1)).1 := by
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have htime := ((T k).list.node_time_lt hi hnext (by omega)).le
  have hstart := (T k).list.node_time_mem hi
  have hend := (T k).list.node_time_mem hnext
  have hpath := (H.segment k).path_smooth.mono
    (Icc_subset_Icc ((H.segment k).lower_pos.le.trans hstart.1)
      (hend.2.trans (H.segment k).upper_lt_one.le))
  obtain ⟨_, _, _, J⟩ := (T k).list.node_edge hi hnext
  have hedge := J.balanced_center_distance.1.trans
    (M13.edist_le_pathELength ((E (k + H.shift)).flow.metric
      (E (k + H.shift)).time) hpath ((T k).list.node_center hi)
        ((T k).list.node_center hnext) htime)
  have hlength := M13.homothety_pathELength
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    (H.normalizedSliceMetric k) (Diffeomorph.refl (𝓡 3) _ ∞) Q hQ
    (M13.identity_metricHomothety _ Q hQ) (H.segment k).path
    ((T k).list.node i).1 ((T k).list.node (i + 1)).1 hpath
  change (H.normalizedSliceMetric k).pathELength (H.segment k).path _ _ = _ at hlength
  rw [hlength]
  calc
    _ = ENNReal.ofReal (Real.sqrt Q) * ENNReal.ofReal
        ((0.99 : ℝ) * ((T k).list.node i).2.scale * epsilon⁻¹) := by
      rw [← ENNReal.ofReal_mul (Real.sqrt_nonneg Q)]
      congr 1
      dsimp only [tubeNodeScale, Q]
      ring
    _ ≤ _ := mul_le_mul_right hedge _

theorem tube_prefix_scale_cost_le (n : ℕ) (hn : n < (T k).list.nodes.length) :
    ENNReal.ofReal (∑ i ∈ Finset.range n,
      (0.99 : ℝ) * H.tubeNodeScale T k (i : ℤ) * epsilon⁻¹) ≤
        (H.normalizedSliceMetric k).pathELength (H.segment k).path
          (H.segment k).lower ((T k).list.node (n : ℤ)).1 := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) :
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier → Type _) :=
    ⟨(H.normalizedSliceMetric k).toRiemannianMetric⟩
  have heps : 0 < epsilon := (H.segment k).cover_epsilon ▸ (H.segment k).cover.epsilon_pos
  have hcost (i : ℕ) : 0 ≤ (0.99 : ℝ) * H.tubeNodeScale T k (i : ℤ) * epsilon⁻¹ :=
    mul_nonneg (mul_nonneg (by norm_num) (H.tubeNodeScale_pos T k _).le)
      (inv_pos.mpr heps).le
  induction n with
  | zero => simp only [Finset.sum_range_zero, ENNReal.ofReal_zero, zero_le]
  | succ n ih =>
    have hi : (n : ℤ) ∈ (T k).list.active := by
      change 0 ≤ (n : ℤ) ∧ (n : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
      omega
    have hnext : (n : ℤ) + 1 ∈ (T k).list.active := by
      change 0 ≤ (n : ℤ) + 1 ∧ (n : ℤ) + 1 ≤ ((T k).list.nodes.length : ℤ) - 1
      omega
    rw [Finset.sum_range_succ, ENNReal.ofReal_add
      (Finset.sum_nonneg (fun i _ => hcost i)) (hcost n)]
    have hadd := Manifold.pathELength_add (I := 𝓡 3) (γ := (H.segment k).path)
      ((T k).list.node_time_mem hi).1
      (((T k).list.node_time_lt hi hnext (by omega)).le)
    exact (add_le_add (ih (by omega))
      (H.tube_edge_scale_cost_le T k hi hnext)).trans_eq (by
        simpa only [RiemannianMetric.pathELength, Nat.cast_add, Nat.cast_one] using hadd)

theorem tube_scale_sum_bound :
    ∑ i ∈ Finset.range ((T k).list.nodes.length - 1),
        H.tubeNodeScale T k (i : ℤ) <
      epsilon * (A + 2 * endpointConnectorBudget epsilon C) / (0.99 : ℝ) := by
  let m := (T k).list.nodes.length - 1
  have hlen : 0 < (T k).list.nodes.length := List.length_pos_iff.mpr (T k).list.nonempty
  have hm : m < (T k).list.nodes.length := by omega
  have hactive : (m : ℤ) ∈ (T k).list.active := by
    change 0 ≤ (m : ℤ) ∧ (m : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
    omega
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) :
      ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier → Type _) :=
    ⟨(H.normalizedSliceMetric k).toRiemannianMetric⟩
  have hlength := (H.tube_prefix_scale_cost_le T k m hm).trans
    (Manifold.pathELength_mono le_rfl ((T k).list.node_time_mem hactive).2)
  have hreal := (ENNReal.ofReal_lt_ofReal_iff'.mp
    (hlength.trans_lt (H.normalizedSlice_path_length_lt k))).1
  have heps : 0 < epsilon := (H.segment k).cover_epsilon ▸ (H.segment k).cover.epsilon_pos
  have hsum : (∑ i ∈ Finset.range m,
      (0.99 : ℝ) * H.tubeNodeScale T k (i : ℤ) * epsilon⁻¹) =
        (0.99 : ℝ) * (∑ i ∈ Finset.range m, H.tubeNodeScale T k (i : ℤ)) *
          epsilon⁻¹ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  rw [hsum] at hreal
  have h := mul_lt_mul_of_pos_right hreal heps
  rw [mul_assoc, inv_mul_cancel₀ heps.ne', mul_one] at h
  exact (lt_div_iff₀ (by norm_num : (0 : ℝ) < 0.99)).mpr (by nlinarith only [h])

end PoincareConjecture.M28.CounterexampleNeckFamily
