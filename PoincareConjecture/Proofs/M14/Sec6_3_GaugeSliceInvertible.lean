import PoincareConjecture.Proofs.M14.Sec6_3_GaugeParameterDifferential
import PoincareConjecture.Definitions.M14Exponential

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}

private theorem horizontal_t2Space : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

private theorem horizontal_bijective_iff_heq {p q : G.Point} (h : p = q)
    (A : G.Horizontal x →L[ℝ] G.Horizontal p) (B : G.Horizontal x →L[ℝ] G.Horizontal q)
    (heq : ∀ W, HEq (A W) (B W)) : Function.Bijective A ↔ Function.Bijective B := by
  cases h
  have hAB : A = B := ContinuousLinearMap.ext (fun W => eq_of_heq (heq W))
  rw [hAB]

theorem exponential_gauge_slice_bijective (E : M14ExponentialFamily G T x)
    (b : G.gaugeCover.index) {U : Set (G.Horizontal x)} (hU : IsOpen U) {C : Set ℝ}
    (β : G.Horizontal x × ℝ →
      (G.timeIntervals.interval (G.gaugeCover.interval b)).Point × G.gaugeCover.spatial b)
    (hrec : ∀ z ∈ U ×ˢ C, (G.gaugeCover.cylinder b).toSpacetime (β z) = E.gamma z.1 z.2)
    {Z : G.Horizontal x} (hZ : Z ∈ U) {s : ℝ} (hs : s ∈ C)
    (hsurv : (Z, s) ∈ E.domain) (hbij : Function.Bijective (E.differential Z s hsurv)) :
    let metric := G.spacetime.horizontalMetric.toRiemannianMetric
    letI : NormedAddCommGroup (G.Horizontal x) :=
      (metric.toCore x).toNormedAddCommGroupOfTopology
        (metric.continuousAt x) (metric.isVonNBounded x)
    letI : InnerProductSpace ℝ (G.Horizontal x) :=
      .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
    letI : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
      ⟨metric⟩
    ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
      (spacetimeModel n) ∞ β (U ×ˢ C) →
    Function.Bijective (fderiv ℝ (fun W => (β (W, s)).2.val) Z) := by
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal x) :=
    (metric.toCore x).toNormedAddCommGroupOfTopology
      (metric.continuousAt x) (metric.isVonNBounded x)
  let : InnerProductSpace ℝ (G.Horizontal x) :=
    .ofCoreOfTopology (metric.toCore x) (metric.continuousAt x) (metric.isVonNBounded x)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) := ⟨metric⟩
  change ContMDiffOn ((𝓘(ℝ, G.Horizontal x)).prod (𝓘(ℝ, ℝ)))
    (spacetimeModel n) ∞ β (U ×ˢ C) →
      Function.Bijective (fderiv ℝ (fun W => (β (W, s)).2.val) Z)
  intro hβ
  have hp : ContMDiffOn (𝓘(ℝ, G.Horizontal x)) (spacetimeModel n) ∞
      (fun W => β (W, s)) U :=
    hβ.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hW => ⟨hW, hs⟩)
  have hβs := (hp.contMDiffAt (hU.mem_nhds hZ)).mdifferentiableAt (by simp)
  have hlocal : (fun W => E.gamma W s) =ᶠ[𝓝 Z]
      fun W => (G.gaugeCover.cylinder b).toSpacetime (β (W, s)) :=
    eventually_nhds_iff.mpr ⟨U, fun W hW => (hrec (W, s) ⟨hW, hs⟩).symm, hU, hZ⟩
  let K := (G.gaugeCover.metric b).spatialTangentEquiv (β (Z, s)).1 (β (Z, s)).2
  let D := fderiv ℝ (fun W => (β (W, s)).2.val) Z
  have hcomp (W : G.Horizontal x) : HEq (E.differential Z s hsurv W) (K (D W)) := by
    have h := gaugeMap_projectedDifferential_congr b hβs hlocal W
    change HEq (G.spacetime.horizontalProjection (E.gamma Z s)
      (M14InitialVectorDerivative G E.gamma s Z W)) (K (D W)) at h
    rw [← E.differential_pointwise_mfderiv Z s hsurv W] at h
    exact (heq_of_eq (G.spacetime.horizontalProjection_identity _
      (E.differential Z s hsurv W)).symm).trans h
  have hKD : Function.Bijective (K.toContinuousLinearMap.comp D) :=
    (horizontal_bijective_iff_heq (hrec (Z, s) ⟨hZ, hs⟩).symm
      (E.differential Z s hsurv) (K.toContinuousLinearMap.comp D) hcomp).mp hbij
  exact (Function.Bijective.of_comp_iff' K.bijective D).mp hKD

end PoincareConjecture.M14
