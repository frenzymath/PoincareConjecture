import PoincareConjecture.Proofs.M14.Sec6_2_SquareCoefficients
import PoincareConjecture.Proofs.M14.Sec6_2_EulerCoordinateMomentum
import PoincareConjecture.Proofs.M08.ClosedChartCoefficients

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

set_option synthInstance.maxSize 2048

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

private theorem momentum_smul {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (B : F →L[ℝ] F →L[ℝ] ℝ) (c : ℝ) (v : F) :
    M08.chartMomentumVector B (c • v) = M08.chartMomentumVector (c • B) v := by
  apply ext_inner_left ℝ
  intro w
  simp only [M08.chartMomentumVector_inner, map_smul, smul_apply]

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

private theorem force_smul
    (DB : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (DV : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) (c : ℝ) (v : EuclideanSpace ℝ (Fin n)) :
    M08.chartForceVector DB (c • DV) (c • v) =
      c • M08.chartForceVector (c • DB) DV v := by
  apply ext_inner_left ℝ
  intro w
  simp only [inner_smul_right, M08.chartForceVector_inner, map_smul, smul_apply, smul_eq_mul]
  ring

theorem squareGauge_coordinate_momentum
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : ∀ t ∈ Ioo τ₁ τ₂, ∀ W : G.Horizontal (p.curve t),
      M14EulerResidual G p E t W = 0)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {a c : ℝ} (hAa : Real.sqrt τ₁ ≤ a) (hcB : c ≤ Real.sqrt τ₂)
    (hsrc : ∀ s ∈ Icc a c, p.curve (s ^ 2) ∈ U) :
    let u := fun s => (lift (p.curve (s ^ 2))).2.val
    let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := squarePotentialCoefficient b (fun s => (lift (p.curve (s ^ 2))).1) x₀
    ∀ s ∈ Ioo a c,
      HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (deriv u r))
        (M08.chartForceVector
          (M08.spatialWithinFDeriv (Icc a c) (G.gaugeCover.spatial b) B (s, u s))
          (M08.spatialWithinFDeriv (Icc a c) (G.gaugeCover.spatial b) V (s, u s))
          (deriv u s)) s := by
  let u₀ := fun t => (lift (p.curve t)).2.val
  let u := fun s => u₀ (s ^ 2)
  let B₀ := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V₀ := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
  let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := squarePotentialCoefficient b (fun s => (lift (p.curve (s ^ 2))).1) x₀
  let DB := M08.spatialWithinFDeriv (Icc a c) (G.gaugeCover.spatial b) B
  let DV := M08.spatialWithinFDeriv (Icc a c) (G.gaugeCover.spatial b) V
  let J := Ioo τ₁ τ₂ ∩ p.curve ⁻¹' U
  let Ω := J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hJ : IsOpen J := p.curve_regular.continuousOn.isOpen_inter_preimage isOpen_Ioo hU
  have hΩ : IsOpen Ω := hJ.prod (G.gaugeCover.spatial b).isOpen
  have hJsub : J ⊆ Ioo τ₁ τ₂ := inter_subset_left
  have hJsrc : ∀ t ∈ J, p.curve t ∈ U := fun _ ht => ht.2
  have hCsub : Icc a c ⊆ M14SqrtParameterInterval τ₁ τ₂ := Icc_subset_Icc hAa hcB
  have hsub : Ioo a c ⊆ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂) := Ioo_subset_Ioo hAa hcB
  have hsnonneg (s : ℝ) (hs : s ∈ Ioo a c) : 0 ≤ s :=
    (Real.sqrt_nonneg τ₁).trans (hsub hs).1.le
  have hτ (s : ℝ) (hs : s ∈ Ioo a c) : s ^ 2 ∈ J :=
    ⟨⟨Real.lt_sq_of_sqrt_lt (hsub hs).1, (Real.lt_sqrt (hsnonneg s hs)).mp (hsub hs).2⟩,
      hsrc s (Ioo_subset_Icc_self hs)⟩
  have hold := euler_gaugeCoordinate_momentum p b lift x₀ hCoordinates hM12 E heuler
    hU hlift hright hJ hJsub hJsrc
  have hdu (s : ℝ) (hs : s ∈ Ioo a c) : HasDerivAt u ((2 * s) • deriv u₀ (s ^ 2)) s := by
    have hd := ((hold.1 _ (hτ s hs)).contDiffAt (hJ.mem_nhds (hτ s hs))).differentiableAt
      (by simp) |>.hasDerivAt
    have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
      simpa using hasDerivAt_pow 2 s
    exact HasDerivAt.scomp (𝕜 := ℝ) s (g₁ := u₀) (h := fun r : ℝ => r ^ 2) hd hsq
  have hpos : ∀ t ∈ J, 0 < t := fun _ ht => p.tau_nonneg.trans_lt (hJsub ht).1
  have htime : ∀ t ∈ J, T - t ∈ (G.gaugeCover.interval b).domain := by
    intro t ht
    rw [← gaugeLift_time_eq p b lift hright (Ioo_subset_Icc_self (hJsub ht)) (hJsrc t ht)]
    exact (lift (p.curve t)).1.property
  have hB₀ : ContDiffOn ℝ ∞ B₀ Ω := backwardMetricCoefficient_contDiffOn
    (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric (G.gaugeCover.metric b).smooth
      T x₀ hpos htime
  have hθ := gaugeLift_time_contMDiffOn p b lift hright
    (hJsub.trans Ioo_subset_Icc_self) hJsrc
  have hV₀ : ContDiffOn ℝ ∞ V₀ Ω :=
    backwardPotentialCoefficient_contDiffOn b _ x₀ hM12 hθ hpos
  obtain ⟨hB, hV⟩ := squareGauge_coefficients_contDiffOn b x₀ p lift hM12 hright hCsub hsrc
  have hBscale (s : ℝ) (hs : 0 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
      B₀ (s ^ 2, z) = (2 * s) • B (s, z) :=
    backwardMetricCoefficient_square (G.gaugeCover.spatial b)
      (G.gaugeCover.metric b).metric T x₀ hs z
  have hVscale (s : ℝ) (hs : 0 ≤ s) (z : EuclideanSpace ℝ (Fin n)) :
      V (s, z) = (2 * s) • V₀ (s ^ 2, z) :=
    squarePotentialCoefficient_eq_backward b (fun t => (lift (p.curve t)).1) x₀ hs z
  change ∀ s ∈ Ioo a c,
    HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (deriv u r))
      (M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (deriv u s)) s
  intro s hs
  have hsC := Ioo_subset_Icc_self hs
  have hx : u s ∈ G.gaugeCover.spatial b := (lift (p.curve (s ^ 2))).2.property
  have hBd := M08.hasFDerivAt_spatialWithin (G.gaugeCover.spatial b).isOpen B hB hsC hx
  have hVd := M08.hasFDerivAt_spatialWithin (G.gaugeCover.spatial b).isOpen V hV hsC hx
  have hB₀d := M08.hasFDerivAt_spatial hΩ B₀ hB₀ (show (s ^ 2, u s) ∈ Ω from ⟨hτ s hs, hx⟩)
  have hV₀d := M08.hasFDerivAt_spatial hΩ V₀ hV₀ (show (s ^ 2, u s) ∈ Ω from ⟨hτ s hs, hx⟩)
  have hDB : M08.spatialFDeriv B₀ (s ^ 2, u s) = (2 * s) • DB (s, u s) := by
    have heq : (fun z => B₀ (s ^ 2, z)) = fun z => (2 * s) • B (s, z) :=
      funext (hBscale s (hsnonneg s hs))
    rw [heq] at hB₀d
    exact hB₀d.unique (hBd.const_smul (2 * s))
  have hDV : DV (s, u s) = (2 * s) • M08.spatialFDeriv V₀ (s ^ 2, u s) := by
    have heq : (fun z => V (s, z)) = fun z => (2 * s) • V₀ (s ^ 2, z) :=
      funext (hVscale s (hsnonneg s hs))
    rw [heq] at hVd
    exact hVd.unique (hV₀d.const_smul (2 * s))
  have hforce : M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (deriv u s) =
      (2 * s) • M08.chartForceVector (M08.spatialFDeriv B₀ (s ^ 2, u₀ (s ^ 2)))
        (M08.spatialFDeriv V₀ (s ^ 2, u₀ (s ^ 2))) (deriv u₀ (s ^ 2)) := by
    rw [(hdu s hs).deriv, hDV, force_smul, ← hDB]
  change HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (deriv u r))
    (M08.chartForceVector (DB (s, u s)) (DV (s, u s)) (deriv u s)) s
  rw [hforce]
  have hsq : HasDerivAt (fun r : ℝ => r ^ 2) (2 * s) s := by
    simpa using hasDerivAt_pow 2 s
  have hchain := HasDerivAt.scomp (𝕜 := ℝ) s (h := fun r : ℝ => r ^ 2)
    (g₁ := fun t => M08.chartMomentumVector (B₀ (t, u₀ t)) (deriv u₀ t))
    (hold.2 _ (hτ s hs)) hsq
  apply hchain.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  change M08.chartMomentumVector (B (r, u r)) (deriv u r) =
    M08.chartMomentumVector (B₀ (r ^ 2, u₀ (r ^ 2))) (deriv u₀ (r ^ 2))
  rw [(hdu r hr).deriv, momentum_smul, ← hBscale r (hsnonneg r hr)]

end PoincareConjecture.M14
