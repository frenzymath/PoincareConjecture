import PoincareConjecture.Proofs.M13.HorizontalLie
import PoincareConjecture.Proofs.M13.HorizontalCurvature
import PoincareConjecture.Proofs.M13.HorizontalConnection
import PoincareConjecture.Proofs.M13.Backward
import PoincareConjecture.Statements.M12GeneralizedEquation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M13

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  {A : AdaptedMetricAtlas n X} {R : GeneralizedFlowCarrierConclusion A}
  {Q : ℝ} {hQ : 0 < Q} {a : ℝ}

theorem parabolicHorizontalCalculus (hEquation : GeneralizedRicciGaugeTheory.{u} n) :
    ParabolicHorizontalCalculus (spacetimeRescaling R Q hQ a) := by
  let P := spacetimeRescaling R Q hQ a
  have hsource := hEquation.leafwise_calculus X A.time A.interval
    R.spacetime R.slices R.timeIntervals R.gaugeCover
  have htarget := hEquation.leafwise_calculus X P.atlasRescaling.atlas.time
    P.atlasRescaling.atlas.interval P.realization.spacetime P.realization.slices
    P.realization.timeIntervals P.realization.gaugeCover
  obtain ⟨D⟩ := hsource.1
  obtain ⟨D'⟩ := htarget.1
  have hlie := parabolic_horizontal_lie D D' (hsource.2 D) (htarget.2 D')
  refine {
    source_connections := ⟨D⟩
    target_connections := ⟨D'⟩
    source_calculus := hsource.2
    target_calculus := htarget.2
    slice_calculus := parabolic_slice_calculus
    normalized_isometry := ⟨normalizedHorizontalIsometry P⟩
    section_smooth_iff := parabolic_section_smooth_iff
    lie_eq := hlie
    riemann_eq := parabolic_horizontal_riemann
    ricci_eq := parabolic_horizontal_ricci
    scalar_eq := parabolic_horizontal_scalar
    norm_eq := parabolic_horizontal_norm
    normSq_eq := parabolic_horizontal_normSq
    equation_iff := ?_
    time_bracket := fun _ _ V _ p _ ↦ parabolic_timeBracket V p
    leafwise_connection := parabolic_leafwise_connection htarget.2
    horizontal_connection := parabolic_horizontal_connection htarget.2
    backward_time := backward_time P
    backward_derivative := backward_mfderiv P
    backward_velocity_val := backward_velocity_val
    backward_velocity := backward_velocity P
    backward_energy := backward_energy P }
  intro D₁ D₂
  constructor
  · intro h p v w
    have hp := h p (P.horizontal p v) (P.horizontal p w)
    rw [hlie, parabolic_horizontal_ricci D₁ D₂] at hp
    exact hp
  · intro h p v w
    obtain ⟨v₀, rfl⟩ := (P.horizontal p).surjective v
    obtain ⟨w₀, rfl⟩ := (P.horizontal p).surjective w
    rw [hlie, parabolic_horizontal_ricci D₁ D₂]
    exact h p v₀ w₀

end PoincareConjecture.M13
