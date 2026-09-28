import PoincareConjecture.Proofs.M47.TerminalCommonIntervalM30Map
import PoincareConjecture.Proofs.M47.LimitNoncollapseSharpTangent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M47

variable {V : GeneralizedBlowupSequence.{u}} {J : Set ℝ}
  (G : GeneralizedBlowupConvergence V J)

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier :=
  G.limit.carrier.isManifold

theorem terminalCommonInterval_m30_terminal_tangent
    {K : Set G.limit.sliceCarrier.carrier} (hK : IsCompact K)
    {lambda : ℝ} (hlambda : 0 < lambda) (hlambda_lt : lambda < 1) :
    ∀ᶠ n : ℕ in atTop,
      let f := terminalCommonInterval_m30TerminalMap G n
      let h : RiemannianMetric 3
          ((V.flow (G.subsequence n)).slice (V.base (G.subsequence n)).1).carrier :=
        M13.scaleSmoothMetric
        ((V.flow (G.subsequence n)).metric (V.base (G.subsequence n)).1)
        (V.scale (G.subsequence n)) (V.base_scalar_pos (G.subsequence n))
      K ⊆ f.source ∧ ∀ x ∈ K, ∀ v : TangentSpace (𝓡 3) x,
        lambda * (G.limit.flow.metric 0).tangentNorm x v ≤
          h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ∧
        h.tangentNorm (f x) (mfderiv (𝓡 3) (𝓡 3) f x v) ≤
          lambda⁻¹ * (G.limit.flow.metric 0).tangentNorm x v := by
  filter_upwards [limitNoncollapse_generalized_compact_tangent_comparison G hK
    0 G.limit.zero_mem hlambda hlambda_lt] with n hn
  refine ⟨?_, ?_⟩
  · rw [(terminalCommonInterval_m30_terminal_source G n).1]
    exact hn.1
  · intro x hx v
    have h0 := hn.2.1
    have hb := hn.2.2 x hx v h0
    have hmap := (terminalCommonInterval_m30_terminal_maps G n h0).1
    have hnorm := congrArg (fun z : (t : ℝ) × (G.limit.sliceCarrier.carrier →
        ((V.flow (G.subsequence n)).slice t).carrier) =>
        ((V.flow (G.subsequence n)).metric z.1).tangentNorm (z.2 x)
          (mfderiv (𝓡 3) (𝓡 3) z.2 x v)) hmap
    dsimp only at hnorm
    rw [← hnorm] at hb
    simp only [M13.scaleSmoothMetric_tangentNorm]
    have hroot : 0 < Real.sqrt (V.scale (G.subsequence n)) :=
      Real.sqrt_pos.mpr (V.base_scalar_pos (G.subsequence n))
    constructor
    · have hl := hb.1
      rw [div_mul_eq_mul_div] at hl
      simpa only [mul_comm] using (le_div_iff₀ hlambda).mp hl
    · calc
        _ ≤ Real.sqrt (V.scale (G.subsequence n)) *
            ((1 / (lambda * Real.sqrt (V.scale (G.subsequence n)))) *
              (G.limit.flow.metric 0).tangentNorm x v) :=
          mul_le_mul_of_nonneg_left hb.2 hroot.le
        _ = _ := by field_simp

end PoincareConjecture.M47
