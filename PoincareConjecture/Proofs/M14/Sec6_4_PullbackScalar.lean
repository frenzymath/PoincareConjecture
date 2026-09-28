import PoincareConjecture.Proofs.M14.Sec6_2_PullbackReparametrization

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {P : ∀ s, G.Horizontal (γ s)}

noncomputable def smulPullbackExtension (E : M14PullbackExtension G γ J P)
    (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) :
    M14PullbackExtension G γ J (fun s => c s • P s) :=
  pullbackExtensionSmulComp E id c contDiff_id hc (fun _ hs => hs)

theorem horizontalCovariantDerivative_smul (E : M14PullbackExtension G γ J P)
    (c : ℝ → ℝ) (hc : ContDiff ℝ ∞ c) {s : ℝ} (hs : s ∈ J) :
    M14HorizontalCovariantDerivative G γ J (fun r => c r • P r)
        (smulPullbackExtension E c hc) s =
      deriv c s • P s + c s • M14HorizontalCovariantDerivative G γ J P E s := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal (γ s)) :=
    (metric.toCore (γ s)).toNormedAddCommGroupOfTopology
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  let : InnerProductSpace ℝ (G.Horizontal (γ s)) :=
    .ofCoreOfTopology (metric.toCore (γ s))
      (metric.continuousAt (γ s)) (metric.isVonNBounded (γ s))
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  have hc' := (hc.differentiable (by simp) s).hasDerivAt
  have hparam : deriv (fun r => c r • E.extension r (γ s)) s =
      c s • deriv (fun r => E.extension r (γ s)) s + deriv c s • P s := by
    simpa only [Pi.smul_def', E.agrees s hs] using
      (hc'.smul hd.differentiableAt.hasDerivAt).deriv
  have hspace := ((E.spatial_smooth s _ (E.graph_mem s hs)).contMDiffAt
    (E.domain_open.mem_nhds (E.graph_mem s hs))).mdifferentiableAt (by simp)
  have hcov := (rawHorizontalCovariantDerivative_isCovariantDerivative G.leafwise).smul_const
    (c s) hspace
  change deriv (fun r => c r • E.extension r (γ s)) s +
    rawHorizontalCovariantDerivative G.leafwise (c s • E.extension s) (γ s)
      (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ)) = _
  rw [hparam, hcov]
  simp only [M14HorizontalCovariantDerivative, smul_apply, smul_add]
  abel

end PoincareConjecture.M14
