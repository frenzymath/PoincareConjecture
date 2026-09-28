import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerODE
import PoincareConjecture.Proofs.M14.Sec6_3_EulerGaugePhase









set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  (b : G.gaugeCover.index)

private theorem gaugeTangent_eq_of_heq
    {z z' : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hz : z = z') {v w : EuclideanSpace ℝ (Fin n)}
    (hv : HEq ((G.gaugeCover.metric b).spatialTangentEquiv z.1 z.2 v)
      ((G.gaugeCover.metric b).spatialTangentEquiv z'.1 z'.2 w)) : v = w := by
  cases hz
  exact ((G.gaugeCover.metric b).spatialTangentEquiv z.1 z.2).injective (eq_of_heq hv)





theorem squareRootEuler_gauge_unique
    (hCoordinates : SpacetimeGaugeTheory.{u, 0} G.leafwise G.timeIntervals)
    (hscalar : ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞
      (horizontalScalarCurvature G.leafwise))
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (hM04 : RicciFlowCurvatureTheory.{0}) (x₀ : G.gaugeCover.spatial b)
    {T τ₁ τ₂ σ₁ σ₂ : ℝ} {x₁ y₁ x₂ y₂ : G.Point}
    {p₁ : M14BackwardPath G T τ₁ τ₂ x₁ y₁} {p₂ : M14BackwardPath G T σ₁ σ₂ x₂ y₂}
    (R₁ : M14SquareRootPath G p₁) (R₂ : M14SquareRootPath G p₂)
    {a c s₀ : ℝ} (hac : a < c)
    (hsub₁ : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂)
    (hsub₂ : Icc a c ⊆ M14SqrtParameterInterval σ₁ σ₂)
    {β₁ β₂ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ₁ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β₁ (Icc a c))
    (hβ₂ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β₂ (Icc a c))
    (hrec₁ : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β₁ s) = R₁.curve s)
    (hrec₂ : ∀ s ∈ Icc a c, (G.gaugeCover.cylinder b).toSpacetime (β₂ s) = R₂.curve s)
    (hclock₁ : ∀ s ∈ Icc a c, (β₁ s).1.val = T - s ^ 2)
    (hclock₂ : ∀ s ∈ Icc a c, (β₂ s).1.val = T - s ^ 2)
    (E₁ : M14PullbackExtension G R₁.curve (M14SqrtParameterInterval τ₁ τ₂)
      R₁.horizontal_velocity)
    (E₂ : M14PullbackExtension G R₂.curve (M14SqrtParameterInterval σ₁ σ₂)
      R₂.horizontal_velocity)
    (heuler₁ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₁.curve s),
      M14SquareRootEulerResidual G R₁ E₁ s Z = 0)
    (heuler₂ : ∀ s ∈ Icc a c, ∀ Z : G.Horizontal (R₂.curve s),
      M14SquareRootEulerResidual G R₂ E₂ s Z = 0)
    (hs₀ : s₀ ∈ Icc a c) (heq : R₁.curve s₀ = R₂.curve s₀)
    (hvel : HEq (R₁.horizontal_velocity s₀) (R₂.horizontal_velocity s₀)) :
    EqOn R₁.curve R₂.curve (Icc a c) := by
  let q₁ := fun s => (β₁ s).2.val
  let q₂ := fun s => (β₂ s).2.val
  let B := M08.chartActionMetric W.flow T x₀
  let P₁ := fun s => M08.chartMomentumVector (B (s, q₁ s)) (derivWithin q₁ (Icc a c) s)
  let P₂ := fun s => M08.chartMomentumVector (B (s, q₂ s)) (derivWithin q₂ (Icc a c) s)
  have hbase : β₁ s₀ = β₂ s₀ := (G.gaugeCover.cylinder b).embedding.injective
    ((hrec₁ s₀ hs₀).trans (heq.trans (hrec₂ s₀ hs₀).symm))
  have hq₀ : q₁ s₀ = q₂ s₀ := congrArg (fun z => z.2.val) hbase
  have hv₁ := squareRootVelocity_gauge_subset b R₁ hsub₁ hβ₁ hrec₁ hs₀
    (uniqueDiffOn_Icc hac s₀ hs₀)
  have hv₂ := squareRootVelocity_gauge_subset b R₂ hsub₂ hβ₂ hrec₂ hs₀
    (uniqueDiffOn_Icc hac s₀ hs₀)
  have hv₀ : derivWithin q₁ (Icc a c) s₀ = derivWithin q₂ (Icc a c) s₀ :=
    gaugeTangent_eq_of_heq b hbase (hv₁.symm.trans (hvel.trans hv₂))
  have hP₀ : P₁ s₀ = P₂ s₀ := by dsimp only [P₁, P₂]; rw [hq₀, hv₀]
  have hphase₁ := squareRootEuler_gauge_phase R₁ b hCoordinates hscalar W hM04 x₀ hac hsub₁
    hβ₁ hrec₁ hclock₁ E₁ heuler₁
  have hphase₂ := squareRootEuler_gauge_phase R₂ b hCoordinates hscalar W hM04 x₀ hac hsub₂
    hβ₂ hrec₂ hclock₂ E₂ heuler₂
  have htime (s : ℝ) (hs : s ∈ Icc a c) : T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [← hclock₁ s hs]
    exact (β₁ s).1.property
  have hsrc (s : ℝ) (_hs : s ∈ Icc a c) : q₁ s ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ (β₁ s).2 = q₁ s := by rw [extChartAt_coe]; rfl
    rw [← hval]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  have hphases := closedChartEulerPhase_unique W.flow hM04 T x₀ hac htime hsrc
    hphase₁ hphase₂ hs₀ (Prod.ext hq₀ hP₀)
  intro s hs
  have hqs : q₁ s = q₂ s := congrArg Prod.fst (hphases hs)
  have hβs : β₁ s = β₂ s := Prod.ext
    (Subtype.ext ((hclock₁ s hs).trans (hclock₂ s hs).symm)) (Subtype.ext hqs)
  exact (hrec₁ s hs).symm.trans ((congrArg (G.gaugeCover.cylinder b).toSpacetime hβs).trans
    (hrec₂ s hs))

end PoincareConjecture.M14
