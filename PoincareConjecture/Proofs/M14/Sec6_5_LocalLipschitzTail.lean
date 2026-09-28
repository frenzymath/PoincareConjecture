import PoincareConjecture.Proofs.M14.Sec6_5_LocalLipschitzDistance

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ : ℝ} {x q0 : G.Point}

theorem exists_terminal_tail_neighborhood (hτ : 0 < τ)
    (htime : G.spacetime.timeFunction q0 = T - τ)
    {U : Set G.Point} (hU : U ∈ 𝓝 q0) {C : ℝ} (hC : 0 ≤ C) :
    ∃ O : Set G.Point, IsOpen O ∧ q0 ∈ O ∧
      ∀ q ∈ O, ∀ p : M14BackwardPath G T 0 (T - G.spacetime.timeFunction q) x q,
        ∀ R : M14SquareRootPath G p,
          (∀ s ∈ M14SqrtParameterInterval 0 (T - G.spacetime.timeFunction q),
            G.spacetime.horizontalMetric.inner (R.curve s)
              (R.horizontal_velocity s) (R.horizontal_velocity s) + 4 * s ^ 2 ≤ C ^ 2) →
          τ < T - G.spacetime.timeFunction q → p.curve τ ∈ U := by
  obtain ⟨ε, hε, hεU⟩ := auxiliarySpacetimeEDist_ball_subset G.spacetime hU
  have ht : ContMDiff (spacetimeModel n) 𝓘(ℝ) ∞ G.spacetime.timeFunction :=
    G.spacetime.time_smooth
  have htimec : Continuous G.spacetime.timeFunction := ht.continuous
  let d : G.Point → ℝ := fun q =>
    C * (Real.sqrt (T - G.spacetime.timeFunction q) - Real.sqrt τ)
  have hdc : Continuous d := continuous_const.mul
    ((Real.continuous_sqrt.comp (continuous_const.sub htimec)).sub continuous_const)
  let O := {q | auxiliarySpacetimeEDist G.spacetime q0 q < ENNReal.ofReal (ε / 2)} ∩
    {q | d q < ε / 2}
  have hO : IsOpen O :=
    (isOpen_lt (auxiliarySpacetimeEDist_continuous G.spacetime q0) continuous_const).inter
      (isOpen_lt hdc continuous_const)
  have hq0 : q0 ∈ O := by
    constructor
    · change auxiliarySpacetimeEDist G.spacetime q0 q0 < ENNReal.ofReal (ε / 2)
      rw [auxiliarySpacetimeEDist_self]
      exact ENNReal.ofReal_pos.mpr (half_pos hε)
    · change C * (Real.sqrt (T - G.spacetime.timeFunction q0) - Real.sqrt τ) < ε / 2
      rw [htime, sub_sub_cancel, sub_self, mul_zero]
      exact half_pos hε
  refine ⟨O, hO, hq0, ?_⟩
  intro q hq p R henergy hτb
  let b := T - G.spacetime.timeFunction q
  have hb : 0 < b := hτ.trans hτb
  have hτr : Real.sqrt τ ∈ M14SqrtParameterInterval 0 b := by
    exact ⟨by simpa only [Real.sqrt_zero] using Real.sqrt_nonneg τ,
      Real.sqrt_le_sqrt hτb.le⟩
  have hbr : Real.sqrt b ∈ M14SqrtParameterInterval 0 b := by
    exact ⟨by simpa only [Real.sqrt_zero] using Real.sqrt_nonneg b, le_rfl⟩
  have hRτ : R.curve (Real.sqrt τ) = p.curve τ := by
    simpa only [Real.sq_sqrt hτ.le] using R.agrees (Real.sqrt τ) hτr
  have hRb : R.curve (Real.sqrt b) = q := by
    simpa only [Real.sq_sqrt hb.le] using
      (R.agrees (Real.sqrt b) hbr).trans
        (by simpa only [Real.sq_sqrt hb.le] using p.curve_end)
  have htail := auxiliarySpacetimeEDist_squareRoot_le R hτr.1 le_rfl
    (Real.sqrt_le_sqrt hτb.le) hC (fun s hs => henergy s
      ⟨hτr.1.trans hs.1.le, hs.2.le⟩)
  rw [hRτ, hRb, auxiliarySpacetimeEDist_comm] at htail
  apply hεU
  calc
    auxiliarySpacetimeEDist G.spacetime q0 (p.curve τ) ≤
        auxiliarySpacetimeEDist G.spacetime q0 q +
          auxiliarySpacetimeEDist G.spacetime q (p.curve τ) :=
      auxiliarySpacetimeEDist_triangle G.spacetime q0 q (p.curve τ)
    _ ≤ auxiliarySpacetimeEDist G.spacetime q0 q + ENNReal.ofReal (d q) :=
      add_le_add le_rfl htail
    _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      ENNReal.add_lt_add hq.1 ((ENNReal.ofReal_lt_ofReal_iff (half_pos hε)).mpr hq.2)
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (half_pos hε).le (half_pos hε).le]
      congr 1
      ring

end PoincareConjecture.M14
