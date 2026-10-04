import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Compact.ParameterNeighborhood
import PoincareLib.Geometry.CurveShortening.Ramp.Analysis.Periodic.GaussianDuhamel

/-!
# Uniform initial heat trace on compact families

Joint continuity of the actual periodic Gaussian action gives one
initial-time radius for a compact family of continuous functions.
MT2007 Claim 19.1, p. 437;
`2026-09-22-c2-compact-initial-heat-trace.md`.
-/

set_option autoImplicit false

open Set
open scoped Topology

namespace PoincareMT.M63

/-- The actual Gaussian heat action tends uniformly to the identity on
a compact family. MT2007 Claim 19.1, p. 437; compact-initial-heat-trace
derivation. No operator-norm continuity or nonempty family is needed. -/
theorem periodicGaussianHeat_uniform_initial_trace
    {L : ℝ} [Fact (0 < L)] {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    {K : Set C(AddCircle L, E)} (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ τ : ℝ, |τ| < δ → ∀ f ∈ K,
      ‖periodicGaussianHeat τ f - f‖ < ε := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let D : ℝ × K → C(AddCircle L, E) :=
    fun p => periodicGaussianHeat p.1 p.2.1 - p.2.1
  have hD : Continuous D :=
    (continuous_periodicGaussianHeat_action.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))).sub
      (continuous_subtype_val.comp continuous_snd)
  have hzero (f : K) : D (0, f) ∈ Metric.ball (0 : C(AddCircle L, E)) ε := by
    simpa only [D, (periodicGaussianHeat_properties f.1).2.1, sub_self,
      Metric.mem_ball, dist_self] using hε
  obtain ⟨δ, hδ, hnear⟩ := exists_uniform_open_parameter_radius hD Metric.isOpen_ball hzero
  refine ⟨δ, hδ, fun τ hτ f hf => ?_⟩
  simpa only [D, Metric.mem_ball, dist_zero_right] using
    hnear τ (by simpa only [Real.dist_eq, sub_zero] using hτ) ⟨f, hf⟩

end PoincareMT.M63
