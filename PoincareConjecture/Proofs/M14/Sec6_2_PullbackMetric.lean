import PoincareConjecture.Proofs.M14.Mathlib.ScalarGraphDerivative
import PoincareConjecture.Definitions.M14PathCalculus
import PoincareConjecture.Proofs.M12.Geometry.Spacetime.Horizontal.Connection
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {γ : ℝ → G.Point} {J : Set ℝ} {Y : ∀ s, G.Horizontal (γ s)}

set_option maxHeartbeats 1000000 in

theorem pullbackExtension_metric_pair_contMDiffAt
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (W : HorizontalSection G.spacetime)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) p (W p)) (γ s)) :
    ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × G.Point => G.spacetime.horizontalMetric.inner z.2
        (E.extension z.1 z.2) (W z.2)) (s, γ s) := by
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
  have hfield := (hE (s, γ s) (hgraph s hs)).contMDiffAt (hU.mem_nhds (hgraph s hs))
  have htest := hW.comp (s, γ s)
    (show ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n)) (spacetimeModel n) ∞
      (Prod.snd : ℝ × G.Point → G.Point) (s, γ s) from contMDiffAt_snd)
  have h : ContMDiffAt ((𝓘(ℝ, ℝ)).prod (spacetimeModel n))
      ((spacetimeModel n).prod 𝓘(ℝ, ℝ)) ∞
      (fun z : ℝ × G.Point => Bundle.TotalSpace.mk' ℝ
        (E := Bundle.Trivial G.Point ℝ) z.2
        (G.spacetime.horizontalMetric.inner z.2 (E.extension z.1 z.2) (W z.2)))
      (s, γ s) := by
    apply ContMDiffAt.clm_bundle_apply₂
      (F₁ := EuclideanSpace ℝ (Fin n)) (F₂ := EuclideanSpace ℝ (Fin n))
    · exact hmetric
    · exact hfield
    · exact htest
  simpa only [Bundle.Trivial.fiberBundle_trivializationAt', Bundle.Trivial.trivialization_apply]
    using (Bundle.contMDiffAt_totalSpace.mp h).2

theorem horizontalCovariantDerivative_metric_derivative
    (E : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s)
    (W : HorizontalSection G.spacetime)
    (hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) p (W p)) (γ s)) :
    HasDerivWithinAt
      (fun r => G.spacetime.horizontalMetric.inner (γ r)
        (E.extension r (γ r)) (W (γ r)))
      (G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (W (γ s)) +
        G.spacetime.horizontalMetric.inner (γ s) (Y s)
          (rawHorizontalCovariantDerivative G.leafwise W (γ s)
            (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) -
        2 * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) *
          horizontalRicci G.leafwise (γ s) (Y s) (W (γ s))) J s := by
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨G.spacetime.horizontalMetric.toRiemannianMetric⟩
  have hEs := ((E.spatial_smooth s (γ s) (E.graph_mem s hs)).contMDiffAt
    (E.domain_open.mem_nhds (E.graph_mem s hs))).mdifferentiableAt (by simp)
  have hspace := rawHorizontalCovariantDerivative_metric_defect G.leafwise hEs
    (hW.mdifferentiableAt (by simp))
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))
  rw [G.ricciEquation, E.agrees s hs] at hspace
  let clock : ℝ := mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
    (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))
  change _ = clock * (-2 * horizontalRicci G.leafwise (γ s) (Y s) (W (γ s))) at hspace
  obtain ⟨d, hd⟩ := E.parameter_derivative s hs
  have hpair := ((G.spacetime.horizontalMetric.inner (γ s)).flip (W (γ s))).hasFDerivAt
    (x := E.extension s (γ s))
  have htime := hpair.comp_hasDerivAt s hd.differentiableAt.hasDerivAt
  change HasDerivAt (fun r => G.spacetime.horizontalMetric.inner (γ s)
      (E.extension r (γ s)) (W (γ s)))
    (G.spacetime.horizontalMetric.inner (γ s)
      (deriv (fun r => E.extension r (γ s)) s) (W (γ s))) s at htime
  have h := scalar_graph_hasDerivWithinAt _
    ((pullbackExtension_metric_pair_contMDiffAt E hs W hW).mdifferentiableAt (by simp)) hγ hJ
  rw [htime.deriv] at h
  have hvalue : G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E s) (W (γ s)) +
        G.spacetime.horizontalMetric.inner (γ s) (Y s)
          (rawHorizontalCovariantDerivative G.leafwise W (γ s)
            (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) -
        2 * (show ℝ from mfderiv (spacetimeModel n) 𝓘(ℝ) G.spacetime.timeFunction (γ s)
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ))) *
          horizontalRicci G.leafwise (γ s) (Y s) (W (γ s)) =
      G.spacetime.horizontalMetric.inner (γ s)
        (deriv (fun r => E.extension r (γ s)) s) (W (γ s)) +
      mvfderiv (spacetimeModel n)
        (fun q => G.spacetime.horizontalMetric.inner q (E.extension s q) (W q)) (γ s)
          (mfderivWithin (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s (1 : ℝ)) := by
    simp only [M14HorizontalCovariantDerivative, map_add, add_apply]
    change _ - 2 * clock * horizontalRicci G.leafwise (γ s) (Y s) (W (γ s)) = _
    linear_combination -hspace
  exact hvalue.symm ▸ h

theorem horizontalCovariantDerivative_extension_independent
    (E₁ E₂ : M14PullbackExtension G γ J Y) {s : ℝ} (hs : s ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J s)
    (hγ : MDifferentiableWithinAt (𝓘(ℝ, ℝ)) (spacetimeModel n) γ J s) :
    M14HorizontalCovariantDerivative G γ J Y E₁ s =
      M14HorizontalCovariantDerivative G γ J Y E₂ s := by
  let v := M14HorizontalCovariantDerivative G γ J Y E₁ s -
    M14HorizontalCovariantDerivative G γ J Y E₂ s
  let W := FiberBundle.extend (EuclideanSpace ℝ (Fin n)) v
  have hW : ContMDiffAt (spacetimeModel n)
      ((spacetimeModel n).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n))
        (E := G.Horizontal) p (W p)) (γ s) :=
    FiberBundle.contMDiffAt_extend (spacetimeModel n) (EuclideanSpace ℝ (Fin n)) v
  have h₁ := horizontalCovariantDerivative_metric_derivative E₁ hs hJ hγ W hW
  have h₂ := horizontalCovariantDerivative_metric_derivative E₂ hs hJ hγ W hW
  have h₁' := h₁.congr_of_mem
    (show ∀ r ∈ J, G.spacetime.horizontalMetric.inner (γ r)
        (E₂.extension r (γ r)) (W (γ r)) =
      G.spacetime.horizontalMetric.inner (γ r) (E₁.extension r (γ r)) (W (γ r)) from by
      intro r hr
      rw [E₁.agrees r hr, E₂.agrees r hr]) hs
  have heq := (h₁'.derivWithin hJ).symm.trans (h₂.derivWithin hJ)
  have hWself : W (γ s) = v := FiberBundle.extend_apply_self _ _
  rw [hWself] at heq
  have hz : G.spacetime.horizontalMetric.inner (γ s) v v = 0 := by
    calc
      _ = G.spacetime.horizontalMetric.inner (γ s)
          (M14HorizontalCovariantDerivative G γ J Y E₁ s) v -
          G.spacetime.horizontalMetric.inner (γ s)
            (M14HorizontalCovariantDerivative G γ J Y E₂ s) v :=
        congrArg (fun L : G.Horizontal (γ s) →L[ℝ] ℝ => L v)
          ((G.spacetime.horizontalMetric.inner (γ s)).map_sub _ _)
      _ = 0 := by linarith
  by_contra hne
  exact (ne_of_gt (G.spacetime.horizontalMetric.pos (γ s) v (sub_ne_zero.mpr hne))) hz

end PoincareConjecture.M14
