import PoincareConjecture.Proofs.M14.Sec6_2_MinimizerCoordinates
import Mathlib.Analysis.InnerProductSpace.Calculus

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
  (x₀ : G.gaugeCover.spatial b)

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

theorem minimizing_gauge_momentum_density_derivatives
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : IsOpen J) (hJsub : J ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ J, p.curve t ∈ U) {a c s : ℝ} (hac : a < c) (hacJ : Icc a c ⊆ J)
    (hs : s ∈ Ioo a c) (hη : ContDiff ℝ ∞ η) :
    ∃ d : ℝ,
      HasDerivAt (fun r =>
        backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
          (r, (lift (p.curve r)).2.val) (deriv (fun t => (lift (p.curve t)).2.val) r) (η r)) d s ∧
      HasDerivAt (fun v => M14RawLIntegrand G (supportedBackwardGaugeFamily p b lift η v)
        (projectedCurveVelocity G (supportedBackwardGaugeFamily p b lift η v)) s) d 0 := by
  let u := fun t => (lift (p.curve t)).2.val
  let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
  let q := derivWithin u (Icc a c)
  have hsC := Ioo_subset_Icc_self hs
  have hsJ := hacJ hsC
  have hmomentum := (minimizing_gaugeCoordinate_regularity p b lift x₀ hM12 hmin hU hlift
    hright hJ hJsub hsrc hac hacJ).2 s hsC
  have hηd := (hη.differentiable (by simp) s).hasDerivAt
  have hpair := hηd.inner ℝ (hmomentum.hasDerivAt (Icc_mem_nhds hs.1 hs.2))
  simp only [M08.chartMomentumVector_inner, M08.chartForceVector_inner] at hpair
  let d := M08.spatialFDeriv B (s, u s) (η s) (q s) (q s) / 2 +
    B (s, u s) (q s) (deriv η s) + M08.spatialFDeriv V (s, u s) (η s)
  have hpair' : HasDerivAt (fun r => B (r, u r) (q r) (η r)) d s := by
    convert hpair using 1 <;> first | rfl | dsimp only [d, B, V, u, q]; ring
  have hpairActual : HasDerivAt (fun r => B (r, u r) (deriv u r) (η r)) d s := by
    apply hpair'.congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
    rw [show q r = deriv u r from derivWithin_of_mem_nhds (Icc_mem_nhds hr.1 hr.2)]
  refine ⟨d, hpairActual, ?_⟩
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
  have hmem : (s, u s) ∈ Ω := ⟨hsJ, (lift (p.curve s)).2.property⟩
  have hBd := M08.hasFDerivAt_spatial hΩ B hB hmem
  have hVd := M08.hasFDerivAt_spatial hΩ V hV hmem
  have hform : HasDerivAt
      (fun v : ℝ => B (s, u s + v • η s) (q s + v • deriv η s) (q s + v • deriv η s) / 2 +
        V (s, u s + v • η s)) d 0 := by
    have h := M08.affine_chart_density_hasDerivAt (fun z => B (s, z)) (fun z => V (s, z))
      (M08.spatialFDeriv B (s, u s)) (M08.spatialFDeriv V (s, u s))
      (u s) (η s) (q s) (deriv η s) 0
      (by simpa only [zero_smul, add_zero] using hBd)
      (by simpa only [zero_smul, add_zero] using hVd)
      (fun v w => backwardMetricCoefficient_symm
        (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀ _ v w)
    simpa only [zero_smul, add_zero] using h
  apply hform.congr_of_eventuallyEq
  have hshift : ∀ᶠ v : ℝ in 𝓝 0, u s + v • η s ∈ G.gaugeCover.spatial b := by
    have hc : ContinuousAt (fun v : ℝ => u s + v • η s) 0 := by fun_prop
    exact hc.preimage_mem_nhds ((G.gaugeCover.spatial b).isOpen.mem_nhds
      (by
        change (lift (p.curve s)).2.val + (0 : ℝ) • η s ∈ G.gaugeCover.spatial b
        rw [zero_smul, add_zero]
        exact (lift (p.curve s)).2.property))
  filter_upwards [hshift] with v hv
  have hp := (p.curve_regular s (hJsub hsJ)).contMDiffAt (isOpen_Ioo.mem_nhds (hJsub hsJ))
  have heq : supportedBackwardGaugeFamily p b lift η v =ᶠ[𝓝 s]
      backwardGaugeFamily p b lift η v := by
    filter_upwards [hp.continuousAt.preimage_mem_nhds (hU.mem_nhds (hsrc s hsJ))] with t ht
    exact supportedBackwardGaugeFamily_eq_gauge p b lift η (hright _ ht) v
  rw [rawLIntegrand_projectedVelocity_congr heq]
  have hqs : q s = deriv u s := derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  rw [hqs]
  exact backwardGaugeFamily_quadraticDensity p b lift η x₀ hU hlift hright hη (hJsub hsJ)
    (hsrc s hsJ) hv

end PoincareConjecture.M14
