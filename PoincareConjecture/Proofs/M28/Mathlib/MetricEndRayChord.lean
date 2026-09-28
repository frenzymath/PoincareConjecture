import PoincareConjecture.Proofs.M28.Mathlib.MetricEndRay
import PoincareConjecture.Proofs.M28.Sec10_5_Angles.ChordDefectLimits

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Topology

universe u

namespace PoincareConjecture.M28

variable {X : Type u} [MetricSpace X]
  (E : UniformSpace.Completion X) (alpha : ℝ)

theorem exists_metricEndRay_chord_pseudometric
    (K : MetricEndRay E alpha → MetricEndRay E alpha → ℝ)
    (hK : ∀ P Q : MetricEndRay E alpha, K P Q ∈ Icc (0 : ℝ) 4)
    (hupper : ∀ P Q : MetricEndRay E alpha, ∀ s ∈ Ioo (0 : ℝ) P.length,
      ∀ t ∈ Ioo (0 : ℝ) Q.length,
        chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ K P Q)
    (hlimit : ∀ P Q : MetricEndRay E alpha, Tendsto
      (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
      ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (K P Q))) :
    ∃ m : PseudoMetricSpace (MetricEndRay E alpha),
      letI := m
      (∀ P Q : MetricEndRay E alpha, dist P Q ≤ 2) ∧
      (∀ P Q : MetricEndRay E alpha, Tendsto
        (fun p : ℝ × ℝ => chordDefect (fun s t => dist (P.point s) (Q.point t)) p.1 p.2)
        ((𝓝[>] (0 : ℝ)) ×ˢ (𝓝[>] (0 : ℝ))) (𝓝 (dist P Q ^ 2))) ∧
      (∀ P Q : MetricEndRay E alpha, Tendsto
        (fun h : ℝ => dist (P.point h) (Q.point h) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 (dist P Q))) ∧
      (∀ P Q : MetricEndRay E alpha, ∀ r s : ℝ, 0 < r → 0 < s → Tendsto
        (fun h : ℝ => dist (P.point (h * r)) (Q.point (h * s)) / h)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Real.sqrt ((r - s) ^ 2 + r * s * dist P Q ^ 2)))) ∧
      (∀ P Q : MetricEndRay E alpha, ∀ s ∈ Ioo (0 : ℝ) P.length,
        ∀ t ∈ Ioo (0 : ℝ) Q.length,
          chordDefect (fun u v => dist (P.point u) (Q.point v)) s t ≤ dist P Q ^ 2) ∧
      ∀ P Q : MetricEndRay E alpha,
        dist P Q = 0 ↔ MetricEndRay.SameEndGerm P Q := by
  let delta : MetricEndRay E alpha → MetricEndRay E alpha → ℝ :=
    fun P Q => Real.sqrt (K P Q)
  have hsquare (P Q : MetricEndRay E alpha) : delta P Q ^ 2 = K P Q :=
    (sqrt_chord_limit_bounds (hK P Q)).2
  have hequal (P Q : MetricEndRay E alpha) :
      Tendsto (fun h : ℝ => dist (P.point h) (Q.point h) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 (delta P Q)) :=
    tendsto_equal_radius_distance_of_chordDefect_limit
      (d := fun s t => dist (P.point s) (Q.point t)) P.length_pos Q.length_pos
      (fun _ _ _ _ => dist_nonneg) (hlimit P Q)
  have hself (P : MetricEndRay E alpha) : delta P P = 0 := by
    have hz : Tendsto (fun h : ℝ => dist (P.point h) (P.point h) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [dist_self, zero_div] using
        (tendsto_const_nhds (x := (0 : ℝ)) (f := 𝓝[>] (0 : ℝ)))
    exact tendsto_nhds_unique (hequal P P) hz
  have hcomm (P Q : MetricEndRay E alpha) : delta P Q = delta Q P := by
    have h : Tendsto (fun h : ℝ => dist (P.point h) (Q.point h) / h)
        (𝓝[>] (0 : ℝ)) (𝓝 (delta Q P)) := by
      simpa only [dist_comm] using hequal Q P
    exact tendsto_nhds_unique (hequal P Q) h
  have htriangle (P Q R : MetricEndRay E alpha) :
      delta P R ≤ delta P Q + delta Q R := by
    apply le_of_tendsto_of_tendsto (hequal P R) ((hequal P Q).add (hequal Q R))
    filter_upwards [self_mem_nhdsWithin] with h hh
    simpa only [add_div] using
      div_le_div_of_nonneg_right (dist_triangle (P.point h) (Q.point h) (R.point h)) hh.le
  let m : PseudoMetricSpace (MetricEndRay E alpha) :=
    { dist := delta
      dist_self := hself
      dist_comm := hcomm
      dist_triangle := htriangle }
  refine ⟨m, ?_⟩
  let := m
  have hdist (P Q : MetricEndRay E alpha) : dist P Q = delta P Q := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro P Q
    exact (sqrt_chord_limit_bounds (hK P Q)).1.2
  · intro P Q
    simpa only [hdist, hsquare] using hlimit P Q
  · intro P Q
    exact hequal P Q
  · intro P Q r s hr hs
    simpa only [hdist, hsquare] using
      tendsto_rescaled_distance_of_chordDefect_limit
        (d := fun u v => dist (P.point u) (Q.point v)) P.length_pos Q.length_pos hr hs
        (fun _ _ _ _ => dist_nonneg) (hlimit P Q)
  · intro P Q s hs t ht
    simpa only [hdist, hsquare] using hupper P Q s hs t ht
  · intro P Q
    constructor
    · intro hzero
      have hKzero : K P Q = 0 := by
        rw [← hsquare P Q, ← hdist P Q, hzero]
        norm_num
      let c : ℝ := min (P.length / 2) (Q.length / 2)
      have hc : 0 < c := lt_min (half_pos P.length_pos) (half_pos Q.length_pos)
      have hcP : c < P.length :=
        (min_le_left _ _).trans_lt (half_lt_self P.length_pos)
      have hcQ : c < Q.length :=
        (min_le_right _ _).trans_lt (half_lt_self Q.length_pos)
      refine ⟨c, hc, hcP.le, hcQ.le, ?_⟩
      intro s hs
      have hu := hupper P Q s ⟨hs.1, hs.2.trans_lt hcP⟩
        s ⟨hs.1, hs.2.trans_lt hcQ⟩
      rw [hKzero] at hu
      change (dist (P.point s) (Q.point s) ^ 2 - (s - s) ^ 2) / (s * s) ≤ 0 at hu
      simp only [sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] at hu
      have hsq : dist (P.point s) (Q.point s) ^ 2 ≤ 0 := by
        simpa only [zero_mul] using (div_le_iff₀ (mul_pos hs.1 hs.1)).mp hu
      apply dist_eq_zero.mp
      nlinarith only [hsq, dist_nonneg (x := P.point s) (y := Q.point s)]
    · rintro ⟨c, hc, _hcP, _hcQ, hagree⟩
      have heqzero :
          (fun h : ℝ => dist (P.point h) (Q.point h) / h) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun _ : ℝ => (0 : ℝ)) := by
        filter_upwards [self_mem_nhdsWithin,
          mem_nhdsWithin_of_mem_nhds (Iic_mem_nhds hc)] with h hh hhc
        rw [hagree ⟨hh, hhc⟩, dist_self, zero_div]
      have hz : Tendsto (fun h : ℝ => dist (P.point h) (Q.point h) / h)
          (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
        Filter.Tendsto.congr' heqzero.symm tendsto_const_nhds
      exact tendsto_nhds_unique (hequal P Q) hz

end PoincareConjecture.M28
