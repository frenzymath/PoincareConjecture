import PoincareConjecture.Proofs.M14.Sec6_2_SquareCoordinateMomentum
import PoincareConjecture.Proofs.M14.Mathlib.ClosedPathSubstitution










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
    NormedSpace ℝ
      (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private noncomputable local instance trilinearNormedGroup :
    NormedAddCommGroup (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance trilinearNormedSpace :
    NormedSpace ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ]
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace




theorem squarePath_gauge_momentum_fixed_window
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (F : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p F)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    (hsrc : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂, p.curve (s ^ 2) ∈ U)
    {D : Set ℝ} (hsub : M14SqrtParameterInterval τ₁ τ₂ ⊆ D)
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ D)
    (hclock : ∀ s ∈ D, (θ s).val = T - s ^ 2)
    (v : ℝ → EuclideanSpace ℝ (Fin n))
    (hv : ∀ s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      v s = deriv (fun r => (lift (p.curve (r ^ 2))).2.val) s) :
    let u := fun s => (lift (p.curve (s ^ 2))).2.val
    let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := squarePotentialCoefficient b θ x₀
    ∀ s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂),
      HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (v r))
        (M08.chartForceVector
          (M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) B (s, u s))
          (M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) V (s, u s)) (v s)) s := by
  let C := Icc (Real.sqrt τ₁) (Real.sqrt τ₂)
  have hCD : C ⊆ D := hsub
  let u := fun s => (lift (p.curve (s ^ 2))).2.val
  let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := squarePotentialCoefficient b θ x₀
  let Vp := squarePotentialCoefficient b (fun s => (lift (p.curve (s ^ 2))).1) x₀
  have hB : ContDiffOn ℝ ∞ B (D ×ˢ (G.gaugeCover.spatial b : Set _)) :=
    squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric
      (G.gaugeCover.metric b).smooth T x₀ (fun s hs => by
        rw [← hclock s hs]
        exact (θ s).property)
  have hV : ContDiffOn ℝ ∞ V (D ×ˢ (G.gaugeCover.spatial b : Set _)) :=
    squarePotentialCoefficient_contDiffOn b θ x₀ hM12 hθ
  have hVe : EqOn V Vp (C ×ˢ (G.gaugeCover.spatial b : Set _)) := by
    intro z hz
    have ht : θ z.1 = (lift (p.curve (z.1 ^ 2))).1 := Subtype.ext
      ((hclock z.1 (hsub hz.1)).trans
        (gaugeLift_time_eq p b lift hright (squarePath_parameter_mem p hz.1) (hsrc _ hz.1)).symm)
    simp only [V, Vp, squarePotentialCoefficient, ht]
  have hPd := squareGauge_coordinate_momentum p b lift x₀ hCoordinates hM12 F heuler
    hU hlift hright le_rfl le_rfl hsrc
  dsimp only
  intro s hs
  have hsC : s ∈ C := Ioo_subset_Icc_self hs
  have huS : u s ∈ G.gaugeCover.spatial b := (lift (p.curve (s ^ 2))).2.property
  have hDB := spatialWithinFDeriv_subset_time (G.gaugeCover.spatial b).isOpen B hB hCD hsC huS
  have hDV : M08.spatialWithinFDeriv C (G.gaugeCover.spatial b) Vp (s, u s) =
      M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) V (s, u s) := by
    rw [← spatialWithinFDeriv_subset_time (G.gaugeCover.spatial b).isOpen V hV hCD hsC huS]
    unfold M08.spatialWithinFDeriv
    rw [fderivWithin_congr' hVe ⟨hsC, huS⟩]
  have hd := hPd s hs
  change HasDerivAt (fun r => M08.chartMomentumVector (B (r, u r)) (deriv u r))
    (M08.chartForceVector
      (M08.spatialWithinFDeriv C (G.gaugeCover.spatial b) B (s, u s))
      (M08.spatialWithinFDeriv C (G.gaugeCover.spatial b) Vp (s, u s)) (deriv u s)) s at hd
  have hforce := congrArg₂ (fun A B => M08.chartForceVector A B (deriv u s)) hDB hDV
  have hvelocity := congrArg
    (M08.chartForceVector
      (M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) B (s, u s))
      (M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) V (s, u s))) (hv s hs).symm
  apply (hd.congr_deriv (hforce.trans hvelocity)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  rw [hv r hr]

end PoincareConjecture.M14
