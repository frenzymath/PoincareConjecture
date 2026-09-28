import PoincareConjecture.Definitions.M30ControlledBlowupLimits


























set_option autoImplicit false

open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture

structure RepairedShortControlledBlowupConclusion
    (S : GeneralizedBlowupSequence.{u}) where
  backward_time : ℝ
  backward_time_pos : 0 < backward_time
  convergence : Nonempty (GeneralizedBlowupConvergence S
    (Set.Icc (-backward_time) 0))

structure RepairedLongControlledBlowupConclusion
    (S : GeneralizedBlowupSequence.{u})
    (kappa r₀ : ℝ) (T₀ : ℝ≥0∞) where
  convergence : GeneralizedBlowupConvergence S (blowupBackwardInterval T₀)
  noncollapsed : M30LimitNoncollapsedAtScale convergence.limit kappa r₀
  ancient : ∀ h : T₀ = ⊤,
    Nonempty (M30AncientKappaIdentification (h ▸ convergence.limit) kappa)

def M30ShortLimitStatement (epsilon₀ : ℝ) : Prop :=
  ∀ (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ),
    epsilon ≤ epsilon₀ →
    M30CommonBlowupControls S epsilon C kappa r₀ mu →
    Nonempty (RepairedShortControlledBlowupConclusion S)

def M30LongLimitStatement (epsilon₀ : ℝ) : Prop :=
  ∀ (S : GeneralizedBlowupSequence.{u})
    (epsilon C kappa r₀ mu : ℝ) (T₀ : ℝ≥0∞),
    epsilon ≤ epsilon₀ →
    M30LongBlowupControls S epsilon C kappa r₀ mu T₀ →
    Nonempty (RepairedLongControlledBlowupConclusion S kappa r₀ T₀)

structure RepairedControlledBlowupLimitTheory : Prop where
  geometric_long : ∀ (S : GeneralizedBlowupSequence.{u}) (T₀ : ℝ≥0∞),
    M30GeometricLongControls S T₀ →
    Nonempty (GeneralizedBlowupConvergence S (blowupBackwardInterval T₀))
  limits : ∃ epsilon₀ : ℝ, 0 < epsilon₀ ∧ epsilon₀ ≤ 1 / 400 ∧
    M30ShortLimitStatement.{u} epsilon₀ ∧ M30LongLimitStatement.{u} epsilon₀

end PoincareConjecture
