import PoincareConjecture.Proofs.M14.Sec6_2_PullbackMetric
import Mathlib.Analysis.Calculus.Deriv.Mul

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y Z : ∀ s, G.Horizontal (γ s)}

set_option maxHeartbeats 1000000 in

theorem pullbackExtensions_metric_pair_contMDiffAt
    (E : M14PullbackExtension G γ J Y) (F : M14PullbackExtension G γ J Z)
    {s : ℝ} (hs : s ∈ J) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × G.Point => G.spacetime.horizontalMetric.inner z.2
        (E.extension z.1 z.2) (F.extension z.1 z.2)) (s, γ s) := by
  have hmetric : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod
        𝓘(ℝ, EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk'
        (E := fun p : G.Point => G.Horizontal p →L[ℝ] G.Horizontal p →L[ℝ] ℝ)
        (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
        z.2 (G.spacetime.horizontalMetric.inner z.2)) (s, γ s) :=
    G.spacetime.horizontalMetric.contMDiff.contMDiffAt.comp (s, γ s)
      (show ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (spacetimeModel n) ∞
        (Prod.snd : ℝ × G.Point → G.Point) (s, γ s) from contMDiffAt_snd)
  obtain ⟨U, hU, hgraph, hE⟩ := E.joint_smooth
  obtain ⟨V, hV, hgraphF, hF⟩ := F.joint_smooth
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk' ℝ
        (E := Bundle.Trivial G.Point ℝ) z.2
        (G.spacetime.horizontalMetric.inner z.2
          (E.extension z.1 z.2) (F.extension z.1 z.2))) (s, γ s) := by
    apply ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact hmetric
    · exact (hE _ (hgraph s hs)).contMDiffAt (hU.mem_nhds (hgraph s hs))
    · exact (hF _ (hgraphF s hs)).contMDiffAt (hV.mem_nhds (hgraphF s hs))
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

set_option maxHeartbeats 1000000 in

set_option backward.isDefEq.respectTransparency false in

theorem horizontalCovariantDerivative_metric_product
    (E : M14PullbackExtension G γ J Y) (F : M14PullbackExtension G γ J Z)
    {s : ℝ} (hs : s ∈ J) (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    HasDerivWithinAt (fun r => G.spacetime.horizontalMetric.inner (γ r) (Y r) (Z r))
      (G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (Z s) +
        G.spacetime.horizontalMetric.inner (γ s) (Y s)
          (M14HorizontalCovariantDerivative G γ J Z F s) -
        2 * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) *
          horizontalRicci G.leafwise (γ s) (Y s) (Z s)) J s := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (γ s)) :=
    (metric.toCore (γ s)).toNormedAddCommGroupOfTopology
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  let : InnerProductSpace ℝ (G.Horizontal (γ s)) :=
    .ofCoreOfTopology (metric.toCore (γ s))
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  have hEs := ((E.spatial_smooth s (γ s) (E.graph_mem s hs)).contMDiffAt
    (E.domain_open.mem_nhds (E.graph_mem s hs))).mdifferentiableAt (by simp)
  have hFs := ((F.spatial_smooth s (γ s) (F.graph_mem s hs)).contMDiffAt
    (F.domain_open.mem_nhds (F.graph_mem s hs))).mdifferentiableAt (by simp)
  have hspace := rawHorizontalCovariantDerivative_metric_defect G.leafwise hEs hFs
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))
  rw [G.ricciEquation, E.agrees s hs, F.agrees s hs] at hspace
  let clock : ℝ := mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))
  change _ = clock * (-2 * horizontalRicci G.leafwise (γ s) (Y s) (Z s)) at hspace
  obtain ⟨dE, hdE⟩ := E.parameter_derivative s hs
  obtain ⟨dF, hdF⟩ := F.parameter_derivative s hs
  let g : G.Horizontal (γ s) →L[ℝ] G.Horizontal (γ s) →L[ℝ] ℝ :=
    G.spacetime.horizontalMetric.inner (γ s)
  have hdE' : HasDerivAt (fun r => E.extension r (γ s))
      (deriv (fun r => E.extension r (γ s)) s) s := hdE.differentiableAt.hasDerivAt
  have hdF' : HasDerivAt (fun r => F.extension r (γ s))
      (deriv (fun r => F.extension r (γ s)) s) s := hdF.differentiableAt.hasDerivAt
  have htime : HasDerivAt (fun r => G.spacetime.horizontalMetric.inner (γ s)
      (E.extension r (γ s)) (F.extension r (γ s)))
    (G.spacetime.horizontalMetric.inner (γ s)
        (deriv (fun r => E.extension r (γ s)) s) (F.extension s (γ s)) +
      G.spacetime.horizontalMetric.inner (γ s) (E.extension s (γ s))
        (deriv (fun r => F.extension r (γ s)) s)) s := by
    simpa only [add_comm] using g.hasDerivAt_of_bilinear (fun _ => hdE') (fun _ => hdF')
  have h := scalar_graph_hasDerivWithinAt _
    ((pullbackExtensions_metric_pair_contMDiffAt E F hs).mdifferentiableAt (by simp)) hγ hJ
  rw [htime.deriv, E.agrees s hs, F.agrees s hs] at h
  have hvalue : G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (Z s) +
        G.spacetime.horizontalMetric.inner (γ s) (Y s)
          (M14HorizontalCovariantDerivative G γ J Z F s) -
        2 * clock * horizontalRicci G.leafwise (γ s) (Y s) (Z s) =
      (G.spacetime.horizontalMetric.inner (γ s)
          (deriv (fun r => E.extension r (γ s)) s) (Z s) +
        G.spacetime.horizontalMetric.inner (γ s) (Y s)
          (deriv (fun r => F.extension r (γ s)) s)) +
      mvfderiv (spacetimeModel n)
        (fun q => G.spacetime.horizontalMetric.inner q (E.extension s q) (F.extension s q))
        (γ s) (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ)) := by
    simp only [M14HorizontalCovariantDerivative, map_add, add_apply]
    linear_combination -hspace
  rw [← hvalue] at h
  exact h.congr_of_mem (fun r hr => by rw [E.agrees r hr, F.agrees r hr]) hs

variable {T τ₁ τ₂ : ℝ} {x y : G.Point} {p : M14BackwardPath G T τ₁ τ₂ x y}

set_option backward.isDefEq.respectTransparency false in

theorem squareRoot_velocity_clock (R : M14SquareRootPath G p)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (R.curve s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve
        (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ))) = -(2 * s) := by
  let dt : TangentSpace (spacetimeModel n) (R.curve s) →L[ℝ] ℝ :=
    mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (R.curve s)
  have htime : dt (G.spacetime.timeVector (R.curve s)) = 1 :=
    G.spacetime.timeVector_normalized (R.curve s)
  have hhorizontal : dt (R.horizontal_velocity s).val = 0 :=
    (R.horizontal_velocity s).property
  change dt (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) R.curve
    (M14SqrtParameterInterval τ₁ τ₂) s (1 : ℝ)) = _
  rw [R.derivative_eq s hs, map_add, map_smul, htime, hhorizontal,
    smul_eq_mul, mul_one, add_zero]

theorem squareRoot_covariantDerivative_metric_product (R : M14SquareRootPath G p)
    {Y Z : ∀ s, G.Horizontal (R.curve s)}
    (E : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Y)
    (F : M14PullbackExtension G R.curve (M14SqrtParameterInterval τ₁ τ₂) Z)
    {s : ℝ} (hs : s ∈ M14SqrtParameterInterval τ₁ τ₂) :
    HasDerivWithinAt (fun r => G.spacetime.horizontalMetric.inner (R.curve r) (Y r) (Z r))
      (G.spacetime.horizontalMetric.inner (R.curve s)
          (M14HorizontalCovariantDerivative G R.curve
            (M14SqrtParameterInterval τ₁ τ₂) Y E s) (Z s) +
        G.spacetime.horizontalMetric.inner (R.curve s) (Y s)
          (M14HorizontalCovariantDerivative G R.curve
            (M14SqrtParameterInterval τ₁ τ₂) Z F s) +
        4 * s * horizontalRicci G.leafwise (R.curve s) (Y s) (Z s))
      (M14SqrtParameterInterval τ₁ τ₂) s := by
  have h := horizontalCovariantDerivative_metric_product E F hs
    (uniqueDiffOn_Icc (Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt) s hs)
    ((R.smooth.mono R.interval_subset s hs).mdifferentiableWithinAt (by simp))
  rw [squareRoot_velocity_clock R hs] at h
  convert h using 1
  ring

end PoincareConjecture.M14
