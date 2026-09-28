import PoincareConjecture.Proofs.M14.Sec6_2_GaugeAction
import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerCoordinates

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b) (η : ℝ → EuclideanSpace ℝ (Fin n))

private noncomputable local instance dualNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance dualNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) := ContinuousLinearMap.toNormedSpace

private noncomputable local instance bilinearNormedGroup :
    NormedAddCommGroup
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance bilinearNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance trilinearNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance trilinearNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem hasDerivAt_supportedBackwardGauge_density (x₀ : G.gaugeCover.spatial b)
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : IsOpen J) (hJsub : J ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ J, p.curve t ∈ U) {s : ℝ} (hs : s ∈ J) (hη : ContDiff ℝ ∞ η) :
    let u := fun t => (lift (p.curve t)).2.val
    let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric
      T x₀
    let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
    HasDerivAt (fun v => M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η v)
      (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η v)) s)
      (M08.spatialFDeriv B (s, u s) (η s) (deriv u s) (deriv u s) / 2 +
        B (s, u s) (deriv u s) (deriv η s) + M08.spatialFDeriv V (s, u s) (η s)) 0 := by
  let u := fun t => (lift (p.curve t)).2.val
  let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
  let Ω := J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hΩ : IsOpen Ω := hJ.prod (G.gaugeCover.spatial b).isOpen
  have hpos : ∀ t ∈ J, 0 < t := fun _ ht => p.tau_nonneg.trans_lt (hJsub ht).1
  have htime : ∀ t ∈ J, T - t ∈ (G.gaugeCover.interval b).domain := by
    intro t ht
    rw [← gaugeLift_time_eq p b lift hright (Ioo_subset_Icc_self (hJsub ht)) (hsrc t ht)]
    exact (lift (p.curve t)).1.property
  have hB : ContDiffOn ℝ ∞ B Ω := backwardMetricCoefficient_contDiffOn
    (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric (G.gaugeCover.metric b).smooth
      T x₀ hpos htime
  have hθ := gaugeLift_time_contMDiffOn p b lift hright
    (hJsub.trans Ioo_subset_Icc_self) hsrc
  have hV : ContDiffOn ℝ ∞ V Ω :=
    backwardPotentialCoefficient_contDiffOn b (fun t => (lift (p.curve t)).1) x₀ hM12 hθ hpos
  have hmem : (s, u s) ∈ Ω := ⟨hs, (lift (p.curve s)).2.property⟩
  have hBd := M08.hasFDerivAt_spatial hΩ B hB hmem
  have hVd := M08.hasFDerivAt_spatial hΩ V hV hmem
  have hform := M08.affine_chart_density_hasDerivAt (fun z => B (s, z)) (fun z => V (s, z))
    (M08.spatialFDeriv B (s, u s)) (M08.spatialFDeriv V (s, u s))
    (u s) (η s) (deriv u s) (deriv η s) 0
    (by simpa only [zero_smul, add_zero] using hBd)
    (by simpa only [zero_smul, add_zero] using hVd)
    (fun v w => backwardMetricCoefficient_symm
      (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀ _ v w)
  simp only [zero_smul, add_zero] at hform
  apply hform.congr_of_eventuallyEq
  have hshift : ∀ᶠ v : ℝ in 𝓝 0, u s + v • η s ∈ G.gaugeCover.spatial b := by
    have hc : ContinuousAt (fun v : ℝ => u s + v • η s) 0 := by fun_prop
    exact hc.preimage_mem_nhds ((G.gaugeCover.spatial b).isOpen.mem_nhds
      (by
        change (lift (p.curve s)).2.val + (0 : ℝ) • η s ∈ G.gaugeCover.spatial b
        rw [zero_smul, add_zero]
        exact (lift (p.curve s)).2.property))
  filter_upwards [hshift] with v hv
  have hp := (p.curve_regular s (hJsub hs)).contMDiffAt (isOpen_Ioo.mem_nhds (hJsub hs))
  have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 s]
      backwardGaugeFamily p b lift η v := by
    filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds (hsrc s hs))] with t ht
    exact supportedBackwardGaugeFamily_eq_gauge p b lift η (hright _ ht) v
  rw [rawLIntegrand_projectedVelocity_congr heq]
  exact backwardGaugeFamily_quadraticDensity p b lift η x₀ hU hlift hright hη (hJsub hs)
    (hsrc s hs) hv

end PoincareConjecture.M14
