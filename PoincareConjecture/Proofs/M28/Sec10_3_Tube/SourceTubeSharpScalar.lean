import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceTubeVolume











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily



theorem exists_source_tube_sharp_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        ∀ k (x : ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier),
          x ∈ (T k).carrierOpen →
            (0.99 : ℝ) * (16 * (max C 2) ^ 2) <
              (H.normalizedSliceConnection k).scalarCurvature x := by
  obtain ⟨epsilon₀, hpos, hsmall, hclose⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 100) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon k x hx
  change x ∈ ((T k).carrierOpen : Set _) at hx
  rw [(T k).carrier_eq_iUnion_nodes] at hx
  obtain ⟨i, hi, hx⟩ := mem_iUnion₂.mp hx
  have hactive : (i : ℤ) ∈ (T k).list.active := by
    change 0 ≤ (i : ℤ) ∧ (i : ℤ) ≤ ((T k).list.nodes.length : ℤ) - 1
    have := Finset.mem_range.mp hi
    omega
  let N := ((T k).list.node (i : ℤ)).2
  let D := (E (k + H.shift)).flow.connection (E (k + H.shift)).time
  have hepsN : N.epsilon ≤ epsilon₀ := by
    rw [(T k).list.node_epsilon hactive]
    exact hepsilon
  have herror := (abs_lt.mp (hclose _ _ D N hepsN x hx)).1
  have hcenter := tube.neck_normalized_scalar_center N D
  have hratio : (0.99 : ℝ) * D.scalarCurvature N.center < D.scalarCurvature x := by
    apply (mul_lt_mul_iff_right₀ (sq_pos_of_pos N.scale_pos)).mp
    nlinarith only [herror, hcenter]
  have hband := ((H.segment k).scalar_band ((T k).list.node (i : ℤ)).1
    ((T k).list.node_time_mem hactive)).1
  rw [(T k).list.node_center hactive] at hband
  have hraw := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left hband (by norm_num : (0 : ℝ) ≤ 0.99)) hratio
  rw [H.normalizedSlice_scalar_eq]
  apply (lt_div_iff₀ (H.base_scalar_pos k)).mpr
  simpa only [D, GeneralizedRicciFlowData.scalar, mul_assoc] using hraw




theorem exists_source_tube_fresh_scale_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)), epsilon ≤ epsilon₀ →
        ∀ k (N : EpsilonNeck
          ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)),
          N.center ∈ (T k).carrierOpen →
            Real.sqrt ((E (k + H.shift)).flow.scalar
              ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩) * N.scale <
                (1.01 : ℝ) * (4 * max C 2)⁻¹ := by
  obtain ⟨epsilon₀, hpos, hsmall, hlower⟩ := exists_source_tube_sharp_scalar_accuracy.{u}
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon k N hcenter
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  let r := Real.sqrt Q * N.scale
  have hQ : 0 < Q := H.base_scalar_pos k
  have hr : 0 < r := mul_pos (Real.sqrt_pos.mpr hQ) N.scale_pos
  have hB : 0 < 4 * max C 2 := by
    have := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right C 2)
    positivity
  have hnorm : r ^ 2 * (H.normalizedSliceConnection k).scalarCurvature N.center = 1 := by
    rw [H.normalizedSlice_scalar_eq]
    change r ^ 2 * ((E (k + H.shift)).flow.scalar
      ⟨(E (k + H.shift)).time, N.center⟩ / Q) = 1
    calc
      _ = N.scale ^ 2 * (E (k + H.shift)).flow.scalar
          ⟨(E (k + H.shift)).time, N.center⟩ := by
        dsimp only [r]
        rw [mul_pow, Real.sq_sqrt hQ.le]
        field_simp
      _ = 1 := tube.neck_normalized_scalar_center N
        ((E (k + H.shift)).flow.connection (E (k + H.shift)).time)
  have hbound := mul_lt_mul_of_pos_left (hlower H T hepsilon k N.center hcenter)
    (sq_pos_of_pos hr)
  rw [hnorm] at hbound
  have hsquare : (0.99 : ℝ) * (r * (4 * max C 2)) ^ 2 < 1 := by
    nlinarith only [hbound]
  have hproduct : r * (4 * max C 2) < (1.01 : ℝ) := by
    by_contra h
    have hlarge := le_of_not_gt h
    have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1.01) hlarge
    nlinarith only [hsquare, hsq]
  change r < (1.01 : ℝ) * (4 * max C 2)⁻¹
  rw [← div_eq_mul_inv]
  exact (lt_div_iff₀ hB).mpr hproduct

end PoincareConjecture.M28.CounterexampleNeckFamily
