import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Controls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Worldlines.Neck
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Geometry.Balls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Volume.SmallBalls
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Blowup.Controlled.Theory









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.DeepHorn

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)] [∀ k, MeasurableSpace (M k)]
  [∀ k, BorelSpace (M k)] [∀ k, T2Space (M k)] [∀ k, T3Space (M k)]
  [∀ k, SecondCountableTopology (M k)]
  {F : ℕ → GeneralizedRicciFlowData.{u}} {T : ℕ → ℝ}
  (H : ∀ k, SingularTimeAssumptions (F k) (T k) (M k))
  (Q : ∀ k, SingularLimitConclusion (H k))
  (x : ∀ k, ((Q k).extension.extended.slice (T k)).carrier)
  (hpos : ∀ k, 0 < ((Q k).extension.extended.connection (T k)).scalarCurvature (x k))
  (hdiv : Tendsto (fun k =>
    ((Q k).extension.extended.connection (T k)).scalarCurvature (x k)) atTop atTop)



theorem terminalBlowupSequence_baseBalls_subset_horns
    (hM04 : RicciFlowCurvatureCalculus.{u}) {K B epsilon : ℝ}
    (hK : 0 < K) (hB : 0 < B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (horn : ∀ k, StrongHorn (Q k).extension epsilon)
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      (terminalBlowupSequence H Q x hpos hdiv).baseBall k A ⊆ (horn k).carrier := by
  obtain ⟨d, hd, hconfine⟩ := exists_terminal_horn_ball_radius.{u} hK hB
  intro A _
  have hsmall : Tendsto (fun k => A /
      Real.sqrt (((Q k).extension.extended.connection (T k)).scalarCurvature (x k)))
      atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hdiv)).const_mul A
  filter_upwards [hdiv.eventually (eventually_ge_atTop (2 * K)),
    hsmall.eventually (gt_mem_nhds hd)] with k hhigh hradius
  have hinside := hconfine hM04 (H k) (Q k).extension (hcutoff k)
    (hconstant k) (horn k) (hboundary k) (x k) (hx k) hhigh
  intro y hy
  apply hinside
  exact lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal hradius.le)



noncomputable def terminalBlowupSequence_commonControls
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (hM29 : DenseGeneralizedBoundedDistanceTheory.{u})
    {epsilon C K B : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ Classical.choose hM29.constants)
    (hnecke : 2 * epsilon < 1 / 2) (hC_pos : 0 < C) (hK : 0 < K) (hB : 0 < B)
    (hepsilon : ∀ k, (H k).epsilon = epsilon)
    (hC : ∀ k, (H k).constant = C)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hscale : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (horn : ∀ k, StrongHorn (Q k).extension (2 * epsilon))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    M30CommonBlowupControls (terminalBlowupSequence H Q x hpos hdiv)
      epsilon C neckNoncollapseConstant 1 (1 / 2) := by
  let S := terminalBlowupSequence H Q x hpos hdiv
  have hh := terminalBlowupSequence_boundedDistance_hypotheses H Q x hpos hdiv
    hM04 hepsilon hC (fun k => (hscale k).le)
  have hb := terminalBlowupSequence_boundedDistance_and_compact H Q x hpos hdiv
    hM04 hM29 hepsilon_pos hepsilon_small hC_pos hepsilon hC (fun k => (hscale k).le)
  have hballs := terminalBlowupSequence_baseBalls_subset_horns H Q x hpos hdiv
    hM04 hK hB hcutoff hconstant horn hx hboundary
  have hnecks : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ S.baseBall k A,
        ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 (2 * epsilon),
          N.center = y := by
    intro A hA
    filter_upwards [hballs A hA] with k hk
    intro y hy
    exact (horn k).every_point_neck y (hk hy)
  refine {
    epsilon_pos := hepsilon_pos
    C_pos := hC_pos
    kappa_pos := neckNoncollapseConstant_pos
    radius_pos := by norm_num
    branch := hh.branch
    canonical := hh.canonical
    analytic_constant := B
    analytic_constant_pos := hB
    scalar_gradient_bound := ?_
    scalar_time_derivative_bound := ?_
    balls_compact := hb.2
    noncollapsed_at_zero := ?_
    mu_pos := by norm_num
    maximal_worldlines := maximalBackwardFlowLineSurvival_of_strongNecks S
      (by norm_num) (by norm_num) hnecks }
  · intro k t ht _ y hy v hv
    exact terminalBlowupSequence_scalar_gradient_bound H Q x hpos hdiv
      hM04 hconstant hscale k t ht y hy v hv
  · intro k b t ht _ y hy
    exact terminalBlowupSequence_scalar_time_derivative_bound H Q x hpos hdiv
      hM04 hconstant hscale k b t ht y hy
  · intro A hA
    filter_upwards [hnecks A hA] with k hk
    intro y hy
    obtain ⟨N, rfl⟩ := hk y hy
    exact N.noncollapsed_at_center hnecke 1



theorem terminalBlowupSequence_short_limit
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (hM29 : DenseGeneralizedBoundedDistanceTheory.{u})
    (hM30 : RepairedControlledBlowupLimitTheory.{u})
    {epsilon C K B : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ Classical.choose hM29.constants)
    (hepsilon_limit : epsilon ≤ Classical.choose hM30.limits)
    (hnecke : 2 * epsilon < 1 / 2) (hC_pos : 0 < C) (hK : 0 < K) (hB : 0 < B)
    (hepsilon : ∀ k, (H k).epsilon = epsilon)
    (hC : ∀ k, (H k).constant = C)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (hcutoff : ∀ k, (H k).r₀⁻¹ ^ 2 < K)
    (hscale : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (horn : ∀ k, StrongHorn (Q k).extension (2 * epsilon))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, ∀ y ∈ (horn k).boundary_sphere,
      ((Q k).extension.extended.connection (T k)).scalarCurvature y ≤ K) :
    Nonempty (RepairedShortControlledBlowupConclusion
      (terminalBlowupSequence H Q x hpos hdiv)) := by
  exact (Classical.choose_spec hM30.limits).2.2.1 _ epsilon C
    neckNoncollapseConstant 1 (1 / 2) hepsilon_limit
    (terminalBlowupSequence_commonControls H Q x hpos hdiv hM04 hM29
      hepsilon_pos hepsilon_small hnecke hC_pos hK hB hepsilon hC hconstant
      hcutoff hscale horn hx hboundary)




theorem terminalBlowupSequence_short_limit_of_hornBoundaryBelow
    (hM04 : RicciFlowCurvatureCalculus.{u})
    (hM29 : DenseGeneralizedBoundedDistanceTheory.{u})
    (hM30 : RepairedControlledBlowupLimitTheory.{u})
    {epsilon C B r₀ rho : ℝ} (hepsilon_pos : 0 < epsilon)
    (hepsilon_small : epsilon ≤ Classical.choose hM29.constants)
    (hepsilon_limit : epsilon ≤ Classical.choose hM30.limits)
    (hnecke : 2 * epsilon < 1 / 2) (hC_pos : 0 < C) (hB : 0 < B)
    (hepsilon : ∀ k, (H k).epsilon = epsilon)
    (hC : ∀ k, (H k).constant = C)
    (hconstant : ∀ k, (H k).analytic_constant = B)
    (hradius : ∀ k, (H k).r₀ = r₀)
    (hscale : ∀ k, (H k).r₀⁻¹ ^ 2 <
      4 * (terminalBlowupSequence H Q x hpos hdiv).scale k)
    (horn : ∀ k, StrongHorn (Q k).extension (2 * (H k).epsilon))
    (hx : ∀ k, x k ∈ (horn k).carrier)
    (hboundary : ∀ k, HornBoundaryBelow (horn k) (rho / (2 * (H k).constant))) :
    Nonempty (RepairedShortControlledBlowupConclusion
      (terminalBlowupSequence H Q x hpos hdiv)) := by
  let K : ℝ := max (r₀⁻¹ ^ 2 + 1) ((rho / (2 * C))⁻¹ ^ 2)
  have hK : 0 < K := (by positivity : 0 < r₀⁻¹ ^ 2 + 1).trans_le (le_max_left _ _)
  have hcutoff (k : ℕ) : (H k).r₀⁻¹ ^ 2 < K := by
    rw [hradius k]
    exact (lt_add_one _).trans_le (le_max_left _ _)
  let horn' (k : ℕ) : StrongHorn (Q k).extension (2 * epsilon) :=
    (hepsilon k) ▸ horn k
  have hcarrier (k : ℕ) : (horn' k).carrier = (horn k).carrier := by
    dsimp only [horn']
    generalize hepsilon k = h
    cases h
    rfl
  have hboundary' (k : ℕ) : (horn' k).boundary_sphere = (horn k).boundary_sphere := by
    dsimp only [horn']
    generalize hepsilon k = h
    cases h
    rfl
  apply terminalBlowupSequence_short_limit H Q x hpos hdiv hM04 hM29 hM30
    hepsilon_pos hepsilon_small hepsilon_limit hnecke hC_pos hK hB
    hepsilon hC hconstant hcutoff hscale horn'
  · intro k
    rw [hcarrier]
    exact hx k
  · intro k y hy
    rw [hboundary'] at hy
    have hb := hboundary k y hy
    rw [hC k] at hb
    exact hb.trans (le_max_right _ _)

end PoincareConjecture.DeepHorn
