import PoincareConjecture.Proofs.M28.Sec10_3_Tube.SourceCriticalBallMargin
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CylinderUniformScalar
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.CriticalBallMarginOrScale

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M28.CounterexampleNeckFamily

theorem exists_source_node_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 200 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ {k : ℕ} {i : ℤ},
          i ∈ (T k).chain.shape.active → ∀ x : (T k).carrierOpen,
          x.val ∈ ((T k).chain.neck i).carrier →
          |H.tubeNodeScale T k i ^ 2 *
            (H.tubeConnection T k).scalarCurvature x - 1| < (1 / 100 : ℝ) := by
  obtain ⟨epsilon₀, hpos, hsmall, haccuracy⟩ :=
    tube.exists_cylinder_scalar_accuracy.{u} (delta := 1 / 100) (by norm_num)
  refine ⟨epsilon₀, hpos, hsmall, ?_⟩
  intro epsilon C A E H T hepsilon k i hi x hx
  let N := (T k).chain.neck i
  let Q := (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, (E (k + H.shift)).basepoint⟩
  have hQ : 0 < Q := H.base_scalar_pos k
  have hNsmall : N.epsilon ≤ epsilon₀ := by
    rw [(T k).chain.epsilon_eq i hi]
    exact hepsilon
  have hnode : N = ((T k).list.node i).2 := by
    dsimp only [N]
    rw [(T k).neck_eq]
    exact (T k).list.neckOfList_eq_node i
  have h := haccuracy ((E (k + H.shift)).flow.slice (E (k + H.shift)).time).carrier
    ((E (k + H.shift)).flow.metric (E (k + H.shift)).time)
    ((E (k + H.shift)).flow.connection (E (k + H.shift)).time) N hNsmall x.val hx
  change |N.scale ^ 2 * (E (k + H.shift)).flow.scalar
    ⟨(E (k + H.shift)).time, x.val⟩ - 1| < (1 / 100 : ℝ) at h
  have hscale : H.tubeNodeScale T k i = Real.sqrt Q * N.scale := by
    simp only [tubeNodeScale, hnode, Q]
  rw [hscale, H.tube_scalar_eq T k x, H.normalizedSlice_scalar_eq k x.val]
  change |(Real.sqrt Q * N.scale) ^ 2 *
    ((E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x.val⟩ / Q) - 1| <
      (1 / 100 : ℝ)
  have hcancel : (Real.sqrt Q * N.scale) ^ 2 *
      ((E (k + H.shift)).flow.scalar ⟨(E (k + H.shift)).time, x.val⟩ / Q) =
      N.scale ^ 2 * (E (k + H.shift)).flow.scalar
        ⟨(E (k + H.shift)).time, x.val⟩ := by
    rw [mul_pow, Real.sq_sqrt hQ.le]
    field_simp [hQ.ne']
  rw [hcancel]
  exact h

theorem exists_source_criticalBall_scalar_accuracy :
    ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ (1 / 1000 : ℝ) ∧
      ∀ {epsilon C A : ℝ}
        {E : ∀ n : ℕ, SameTimeCounterexample.{u} epsilon C A
          ((n : ℝ) + 1) ((n : ℝ) + 1)}
        (H : CounterexampleNeckFamily E)
        (T : ∀ k, SourceTubeData (H.segment k)),
        epsilon ≤ epsilon₀ → ∀ {A1 : ℝ},
          (∀ r < A1, tube.eventuallyRadiusBound
            (fun k x => ((H.tubeMetric T k).edist (H.tubeBase T k) x).toReal)
            (fun k x => (H.tubeConnection T k).scalarCurvature x) r) →
          ∀ delta : ℝ, 0 < delta → ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ k in atTop,
            ∀ x ∈ regularPoints (H.tubeCriticalMetric T A1 k) delta,
              (H.tubeConnection T k).scalarCurvature x ≤ K := by
  obtain ⟨epsilonM, hMpos, hMsmall, hmargin⟩ :=
    exists_source_criticalBall_small_scale_margin_accuracy.{u}
  obtain ⟨epsilonS, hSpos, _hSsmall, hscalar⟩ := exists_source_node_scalar_accuracy.{u}
  refine ⟨min epsilonM epsilonS, lt_min hMpos hSpos,
    (min_le_left _ _).trans hMsmall, ?_⟩
  intro epsilon C A E H T hepsilon A1 hcrit delta hdelta
  have hsmallM := hepsilon.trans (min_le_left epsilonM epsilonS)
  have hsmallS := hepsilon.trans (min_le_right epsilonM epsilonS)
  obtain ⟨K, hK⟩ := hcrit (A1 - delta / 2) (by linarith)
  refine ⟨max (max K (2328 / delta ^ 2)) 0, le_max_right _ _, ?_⟩
  filter_upwards [hK] with k hk x hxreg
  have hx : (x : (T k).carrierOpen).val ∈ (T k).tube.carrier := x.val.property
  rw [(T k).carrier_eq] at hx
  change (x : (T k).carrierOpen).val ∈
    ⋃ j : {j // j ∈ (T k).chain.shape.active}, ((T k).chain.neck j.1).carrier at hx
  obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
  by_cases hscale : H.tubeNodeScale T k i.val < delta / 48
  · exact (hk x (hmargin H T hsmallM k x hdelta hxreg i.property hxi hscale)).trans
      ((le_max_left _ _).trans (le_max_left _ _))
  · exact (scalar_le_of_scale_lower_of_accuracy hdelta (le_of_not_gt hscale)
      (hscalar H T hsmallS i.property x hxi)).trans
      ((le_max_right _ _).trans (le_max_left _ _))

end PoincareConjecture.M28.CounterexampleNeckFamily
