import PoincareConjecture.Proofs.M47.TerminalCurvatureFlowInvariants
import PoincareConjecture.Proofs.M47.TerminalCurvatureNormContinuity
import PoincareConjecture.Proofs.M47.TerminalCurvatureSaturation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M47

theorem terminalCurvature_bounded_of_parallel_saturation
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {g : RiemannianMetric n M} (D : LeviCivitaData g)
    {V : (x : M) → TangentSpace (𝓡 n) x} {Phi : ℝ → M → M}
    (hV : ContMDiff (𝓡 n) ((𝓡 n).prod (𝓡 n)) ∞ (T% V))
    (hparallel : ∀ y v, D.connection V y v = 0)
    (hs : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 n)) (𝓡 n) ∞ (fun z : ℝ × M => Phi z.1 z.2))
    (hPhi : ∀ x, IsMIntegralCurve (fun t => Phi t x) V)
    (hzero : ∀ x, Phi 0 x = x)
    (hadd : ∀ s t x, Phi (s + t) x = Phi s (Phi t x))
    {K : Set M} (hK : IsCompact K) (hne : K.Nonempty)
    (hopen : IsOpen {x | ∃ t : ℝ, ∃ k ∈ K, Phi t k = x}) :
    ∃ B : ℝ, 0 < B ∧ ∀ x, D.curvatureTensorNorm x ≤ B := by
  let := g.toMetricSpace
  obtain ⟨B, hB⟩ := terminalCurvature_invariant_bounded_of_compact_saturation
    Phi hzero hadd (terminalCurvature_flow_isometry D hV hparallel hs hPhi hzero hadd)
    hK hne hopen D.curvatureTensorNorm (terminalCurvature_norm_continuous D).continuousOn
    (fun t x => (terminalCurvature_flow_invariants D hV hparallel hs hPhi hzero hadd t).2.1 x)
  exact ⟨max 1 B, lt_of_lt_of_le zero_lt_one (le_max_left _ _),
    fun x => (hB x).trans (le_max_right _ _)⟩

end PoincareConjecture.M47
