import PoincareConjecture.Proofs.M14.Sec6_2_EulerGaugePair
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeDensityDerivative
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

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
    G.gaugeCover.spatial b) (x₀ : G.gaugeCover.spatial b)

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

theorem euler_gaugeCoordinate_momentum
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : ∀ t ∈ Ioo τ₁ τ₂, ∀ W : G.Horizontal (p.curve t),
      M14EulerResidual G p E t W = 0)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : IsOpen J) (hJsub : J ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ J, p.curve t ∈ U) :
    let u := fun t => (lift (p.curve t)).2.val
    let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
    ContDiffOn ℝ ∞ u J ∧ ∀ t ∈ J,
      HasDerivAt (fun s => M08.chartMomentumVector (B (s, u s)) (deriv u s))
        (M08.chartForceVector (M08.spatialFDeriv B (t, u t))
          (M08.spatialFDeriv V (t, u t)) (deriv u t)) t := by
  let u := fun t => (lift (p.curve t)).2.val
  let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
  let P := fun t => M08.chartMomentumVector (B (t, u t)) (deriv u t)
  have hL := hlift.comp ((backwardPath_contMDiffOn_of_velocity_extension p E).mono hJsub) hsrc
  have hval : ContMDiff (𝓡 n) (𝓡 n) ∞
      (Subtype.val : G.gaugeCover.spatial b → EuclideanSpace ℝ (Fin n)) := contMDiff_subtype_val
  have hspace : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun t => (lift (p.curve t)).2) J := fun t ht => (hL t ht).snd
  have hu : ContDiffOn ℝ ∞ u J := (hval.comp_contMDiffOn hspace).contDiffOn
  have hq : ContDiffOn ℝ ∞ (deriv u) J := hu.deriv_of_isOpen hJ (by simp)
  let Ω := J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hpos : ∀ t ∈ J, 0 < t := fun _ ht => p.tau_nonneg.trans_lt (hJsub ht).1
  have htime : ∀ t ∈ J, T - t ∈ (G.gaugeCover.interval b).domain := by
    intro t ht
    rw [← gaugeLift_time_eq p b lift hright (Ioo_subset_Icc_self (hJsub ht)) (hsrc t ht)]
    exact (lift (p.curve t)).1.property
  have hB : ContDiffOn ℝ ∞ B Ω := backwardMetricCoefficient_contDiffOn
    (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric (G.gaugeCover.metric b).smooth
      T x₀ hpos htime
  have hP : ContDiffOn ℝ ∞ P J :=
    (InnerProductSpace.toDual ℝ (EuclideanSpace ℝ (Fin n))).symm.toContinuousLinearEquiv.contDiff
      |>.comp_contDiffOn ((hB.comp (contDiffOn_id.prodMk hu)
        (fun t ht => ⟨ht, (lift (p.curve t)).2.property⟩)).clm_apply hq)
  refine ⟨hu, ?_⟩
  intro s hs
  have hPd := ((hP s hs).contDiffAt (hJ.mem_nhds hs)).differentiableAt (by simp) |>.hasDerivAt
  suffices hforce : deriv P s = M08.chartForceVector (M08.spatialFDeriv B (s, u s))
      (M08.spatialFDeriv V (s, u s)) (deriv u s) by
    simpa only [hforce] using hPd
  apply ext_inner_left ℝ
  intro w
  obtain ⟨ζ, hζs, _, hζ, _, hζone⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞)) (hJ.mem_nhds hs)
  let η := fun t => ζ t • w
  have hη : ContDiff ℝ ∞ η := hζ.smul contDiff_const
  have hηs : η s = w := by simp only [η, hζone, one_smul]
  have hsupp : tsupport η ⊆ J := (tsupport_smul_subset_left ζ (fun _ => w)).trans hζs
  have hdensity := hasDerivAt_supportedBackwardGauge_density p b lift η x₀
    hM12 hU hlift hright hJ hJsub hsrc hs hη
  have hpair := hasDerivAt_supportedBackwardGauge_pair_of_euler p b lift η x₀ hCoordinates hM12
    E hU hlift hright hη (hsupp.trans hJsub) (fun t ht => hsrc t (hsupp ht))
      (hJsub hs) (hsrc s hs) (heuler s (hJsub hs)) hdensity
  have hknown := ((hη.differentiable (by simp) s).hasDerivAt).inner ℝ hPd
  simp only [P, M08.chartMomentumVector_inner] at hknown
  have heq := hknown.unique hpair
  rw [hηs] at heq
  rw [M08.chartForceVector_inner]
  linarith

end PoincareConjecture.M14
