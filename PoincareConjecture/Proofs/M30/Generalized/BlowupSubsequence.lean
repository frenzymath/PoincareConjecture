import PoincareConjecture.Statements.M30ControlledBlowupLimits

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M30

def reindexedBlowupSequence (S : GeneralizedBlowupSequence.{u})
    (phi : ℕ → ℕ) (hphi : StrictMono phi) : GeneralizedBlowupSequence.{u} where
  flow := fun k => S.flow (phi k)
  base := fun k => S.base (phi k)
  base_scalar_pos := fun k => S.base_scalar_pos (phi k)
  scalar_diverges := S.scalar_diverges.comp hphi.tendsto_atTop

def reindexedCommonBlowupControls {S : GeneralizedBlowupSequence.{u}}
    {epsilon C kappa r₀ mu : ℝ}
    (H : M30CommonBlowupControls S epsilon C kappa r₀ mu)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    M30CommonBlowupControls (reindexedBlowupSequence S phi hphi)
      epsilon C kappa r₀ mu where
  epsilon_pos := H.epsilon_pos
  C_pos := H.C_pos
  kappa_pos := H.kappa_pos
  radius_pos := H.radius_pos
  branch := fun k => H.branch (phi k)
  canonical := fun k => H.canonical (phi k)
  analytic_constant := H.analytic_constant
  analytic_constant_pos := H.analytic_constant_pos
  scalar_gradient_bound := fun k => H.scalar_gradient_bound (phi k)
  scalar_time_derivative_bound := fun k => H.scalar_time_derivative_bound (phi k)
  balls_compact := fun A hA => hphi.tendsto_atTop.eventually (H.balls_compact A hA)
  noncollapsed_at_zero := fun A hA =>
    hphi.tendsto_atTop.eventually (H.noncollapsed_at_zero A hA)
  mu_pos := H.mu_pos
  maximal_worldlines := fun A hA =>
    hphi.tendsto_atTop.eventually (H.maximal_worldlines A hA)

def reindexedLongBlowupControls {S : GeneralizedBlowupSequence.{u}}
    {epsilon C kappa r₀ mu : ℝ} {T₀ : ℝ≥0∞}
    (H : M30LongBlowupControls S epsilon C kappa r₀ mu T₀)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    M30LongBlowupControls (reindexedBlowupSequence S phi hphi)
      epsilon C kappa r₀ mu T₀ where
  toM30CommonBlowupControls := reindexedCommonBlowupControls H.toM30CommonBlowupControls phi hphi
  horizon_pos := H.horizon_pos
  slabs := by
    intro T hT hTT A hA
    filter_upwards [hphi.tendsto_atTop.eventually (H.slabs T hT hTT A hA)] with k hk
    obtain ⟨E⟩ := hk
    exact ⟨{
      embedding := E.embedding
      zero_identity := E.zero_identity
      noncollapsed := E.noncollapsed }⟩

theorem reindexed_boundedDistance {S : GeneralizedBlowupSequence.{u}}
    (hbound : GeneralizedBlowupBoundedDistance S)
    (phi : ℕ → ℕ) (hphi : StrictMono phi) :
    GeneralizedBlowupBoundedDistance (reindexedBlowupSequence S phi hphi) := by
  intro A hA
  obtain ⟨D, hD, hevent⟩ := hbound A hA
  exact ⟨D, hD, hphi.tendsto_atTop.eventually hevent⟩

def convergenceOfReindexed {S : GeneralizedBlowupSequence.{u}}
    {phi : ℕ → ℕ} {hphi : StrictMono phi} {J : Set ℝ}
    (G : GeneralizedBlowupConvergence (reindexedBlowupSequence S phi hphi) J) :
    GeneralizedBlowupConvergence S J where
  limit := G.limit
  subsequence := phi ∘ G.subsequence
  subsequence_strictMono := hphi.comp G.subsequence_strictMono
  exhaustion := G.exhaustion
  embedding := G.embedding
  base_preserving := G.base_preserving
  source_balls_in_image := G.source_balls_in_image
  pullback_metric_CInfinity := G.pullback_metric_CInfinity

theorem shortConclusion_of_reindexed {S : GeneralizedBlowupSequence.{u}}
    {phi : ℕ → ℕ} {hphi : StrictMono phi}
    (h : Nonempty (RepairedShortControlledBlowupConclusion
      (reindexedBlowupSequence S phi hphi))) :
    Nonempty (RepairedShortControlledBlowupConclusion S) := by
  obtain ⟨H⟩ := h
  obtain ⟨G⟩ := H.convergence
  exact ⟨{
    backward_time := H.backward_time
    backward_time_pos := H.backward_time_pos
    convergence := ⟨convergenceOfReindexed G⟩ }⟩

def longConclusionOfReindexed {S : GeneralizedBlowupSequence.{u}}
    {phi : ℕ → ℕ} {hphi : StrictMono phi} {kappa r₀ : ℝ} {T₀ : ℝ≥0∞}
    (H : RepairedLongControlledBlowupConclusion
      (reindexedBlowupSequence S phi hphi) kappa r₀ T₀) :
    RepairedLongControlledBlowupConclusion S kappa r₀ T₀ where
  convergence := convergenceOfReindexed H.convergence
  noncollapsed := H.noncollapsed
  ancient := H.ancient

end PoincareConjecture.M30
