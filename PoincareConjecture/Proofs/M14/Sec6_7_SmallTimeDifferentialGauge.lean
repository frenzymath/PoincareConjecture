import PoincareConjecture.Proofs.M14.Sec6_3_InitialVector
import PoincareConjecture.Proofs.M14.Sec6_2_JacobiGaugeFields
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeParameterDifferential











set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ}




theorem exponentialGauge_initial_velocity
    (b : G.gaugeCover.index)
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (E : M14ExponentialFamily G T ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))}
    {S d : ℝ} (hS : 0 < S) (hd : 0 < d) (hdS : d ≤ S)
    (hsurv : (Z, S) ∈ E.domain)
    {β : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b}
    (hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc 0 d))
    (hrec : ∀ s ∈ Icc 0 d, (G.gaugeCover.cylinder b).toSpacetime (β s) = E.gamma Z s)
    (hzero : β 0 = (t₀, x₀)) :
    derivWithin (fun s => (β s).2.val) (Icc 0 d) 0 =
      (2 : ℝ) • ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm Z := by
  let R := E.square_path Z S hsurv hS
  have hsub : Icc 0 d ⊆ M14SqrtParameterInterval 0 (S ^ 2) := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hS.le]
    exact Icc_subset_Icc le_rfl hdS
  have hrecR (s : ℝ) (hs : s ∈ Icc 0 d) :
      (G.gaugeCover.cylinder b).toSpacetime (β s) = R.curve s :=
    (hrec s hs).trans (exponential_square_curve_eq E Z hsurv hS (hsub hs)).symm
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd.le⟩
  have hv := squareRootVelocity_gauge_subset b R hsub hβ hrecR h0
    (uniqueDiffOn_Icc hd 0 h0)
  rw [hzero] at hv
  obtain ⟨hstart, hinit⟩ := E.square_initial_velocity Z S hsurv hS
  have hi : HEq (R.horizontal_velocity 0) ((2 : ℝ) • Z) :=
    (eqRec_heq hstart (R.horizontal_velocity 0)).symm.trans (heq_of_eq hinit)
  apply ((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).injective
  rw [map_smul, ContinuousLinearEquiv.apply_symm_apply]
  exact eq_of_heq (hv.symm.trans hi)




theorem exponentialGauge_differential_heq {x : G.Point}
    (E : M14ExponentialFamily G T x) {Z : G.Horizontal x} {s : ℝ}
    (hs : (Z, s) ∈ E.domain) (b : G.gaugeCover.index)
    (β : G.Horizontal x → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b) (W : G.Horizontal x) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    MDifferentiableAt (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) β Z →
    (fun A => E.gamma A s) =ᶠ[𝓝 Z]
      (fun A => (G.gaugeCover.cylinder b).toSpacetime (β A)) →
    HEq (E.differential Z s hs W)
      ((G.gaugeCover.metric b).spatialTangentEquiv (β Z).1 (β Z).2
        (fderiv ℝ (fun A => (β A).2.val) Z W)) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  dsimp only
  intro hβ hrec
  have hp : G.spacetime.horizontalProjection (E.gamma Z s)
      (mfderiv (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n)
        (fun A => E.gamma A s) Z W) = E.differential Z s hs W := by
    change G.spacetime.horizontalProjection (E.gamma Z s)
      (M14InitialVectorDerivative G E.gamma s Z W) = E.differential Z s hs W
    rw [← E.differential_pointwise_mfderiv Z s hs W]
    exact G.spacetime.horizontalProjection_identity _ _
  exact (heq_of_eq hp).symm.trans (gaugeMap_projectedDifferential_congr b hβ hrec W)

end PoincareConjecture.M14
