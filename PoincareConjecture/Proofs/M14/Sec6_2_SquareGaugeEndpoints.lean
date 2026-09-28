import PoincareConjecture.Proofs.M14.Sec6_2_SquareCoordinateMomentum
import PoincareConjecture.Proofs.M14.Sec6_2_SquareGaugeEnergy
import PoincareConjecture.Proofs.M14.Mathlib.FiniteQuadraticMomentum

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point} (p : M14BackwardPath G T τ₁ τ₂ x y)
  (b : G.gaugeCover.index)
  (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
    G.gaugeCover.spatial b)

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

theorem squareGauge_spatial_contDiffOn
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (hac : a < c) (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U) :
    ContDiffOn ℝ ∞ (fun s => (lift (p.curve (s ^ 2))).2.val) (Icc a c) := by
  let u := fun s => (lift (p.curve (s ^ 2))).2.val
  let x₀ := (lift (p.curve (a ^ 2))).2
  let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := squarePotentialCoefficient b (fun s => (lift (p.curve (s ^ 2))).1) x₀
  obtain ⟨hB, hV⟩ := squareGauge_coefficients_contDiffOn b x₀ p lift hM12 hright
    (Icc_subset_Icc hAa hcB) hsrc
  obtain ⟨hu, hud, hd⟩ := squarePath_gauge_derivative_memLp p b lift hM12 hlift hright
    hac hAa hcB hsrc
  have hPd := squareGauge_coordinate_momentum p b lift x₀ hCoordinates hM12 E heuler
    hU hlift hright hAa hcB hsrc
  exact (ODE.contDiffOn_of_finite_quadratic_momentum hac (G.gaugeCover.spatial b).isOpen B V
    hB hV (fun z hz v hv => squareMetricCoefficient_pos (G.gaugeCover.spatial b)
      (G.gaugeCover.metric b).metric T x₀ z.1 hz.2 v hv) u (deriv u) hu
        (fun s _ => (lift (p.curve (s ^ 2))).2.property) hud hd hPd).1

theorem squareGauge_curve_contMDiffOn
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p E)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (hac : a < c) (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ (fun s => p.curve (s ^ 2)) (Icc a c) := by
  have hu := squareGauge_spatial_contDiffOn p b lift hCoordinates hM12 E heuler
    hU hlift hright hac hAa hcB hsrc
  have hspace : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 n) ∞
      (fun s => (lift (p.curve (s ^ 2))).2) (Icc a c) := by
    intro s hs
    exact (ContMDiffWithinAt.subtypeVal_comp_iff (G.gaugeCover.spatial b) _ _ s).mp
      (hu.contMDiffOn s hs)
  have hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞
      (fun s => (lift (p.curve (s ^ 2))).1) (Icc a c) := by
    apply intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
      (G.timeIntervals.interval (G.gaugeCover.interval b))
    have hc : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ)) ∞ (fun s : ℝ => T - s ^ 2) (Icc a c) :=
      (contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn
    exact hc.congr (fun s hs => gaugeLift_time_eq p b lift hright
      (squarePath_parameter_mem p (Icc_subset_Icc hAa hcB hs)) (hsrc s hs))
  have hcyl := (G.gaugeCover.cylinder b).smooth.comp_contMDiffOn (hθ.prodMk hspace)
  exact hcyl.congr (fun s hs => (hright _ (hsrc s hs)).symm)

end PoincareConjecture.M14
