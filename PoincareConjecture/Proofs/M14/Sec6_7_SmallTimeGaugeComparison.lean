import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeGaugeAction
import PoincareConjecture.Proofs.M14.Sec6_7_SmallTimeGaugeMomentum
import PoincareConjecture.Proofs.M14.Sec6_2_SquareGaugeEndpoints
import PoincareConjecture.Proofs.M14.Mathlib.QuadraticShortTimeMinimality

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 2048

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle NNReal Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T τ₁ τ₂ : ℝ} {x y : G.Point}

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

theorem squarePath_gauge_action_comparison
    (hCoordinates : M12MetricPredecessors.{0} n) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (p q : M14BackwardPath G T τ₁ τ₂ x y)
    (F : M14PullbackExtension G p.curve (Ioo τ₁ τ₂) p.horizontal_velocity)
    (heuler : M14EulerEquation G p F)
    (b : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point ×
      G.gaugeCover.spatial b) (x₀ : G.gaugeCover.spatial b)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ z ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift z) = z)
    {D : Set ℝ} (hD : UniqueDiffOn ℝ D) (hsub : M14SqrtParameterInterval τ₁ τ₂ ⊆ D)
    (θ : ℝ → (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (hθ : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ θ D)
    (hclock : ∀ s ∈ D, (θ s).val = T - s ^ 2)
    {S : Set (EuclideanSpace ℝ (Fin n))} (hS : Convex ℝ S)
    (hSU : S ⊆ G.gaugeCover.spatial b) {m M : ℝ} (hm : 0 < m) (K : ℝ≥0)
    (hp : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      p.curve (s ^ 2) ∈ U ∧ (lift (p.curve (s ^ 2))).2.val ∈ S)
    (hq : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      q.curve (s ^ 2) ∈ U ∧ (lift (q.curve (s ^ 2))).2.val ∈ S)
    (hspeed : ∀ s ∈ M14SqrtParameterInterval τ₁ τ₂,
      ‖derivWithin (fun r => (lift (p.curve (r ^ 2))).2.val)
        (M14SqrtParameterInterval τ₁ τ₂) s‖ ≤ M) :
    let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := squarePotentialCoefficient b θ x₀
    (∀ z ∈ D ×ˢ S, ∀ v : EuclideanSpace ℝ (Fin n), m * ‖v‖ ^ 2 ≤ B z v v) →
    (∀ s ∈ D, LipschitzOnWith K (fun z => B (s, z)) S ∧
      LipschitzOnWith K (fun z => M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) B (s, z)) S ∧
      LipschitzOnWith K (fun z => M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) V (s, z)) S) →
    0 < m / 4 - ((K : ℝ) * M ^ 2 / 2 + K + ((K : ℝ) * M) ^ 2 / m) *
      (Real.sqrt τ₂ - Real.sqrt τ₁) ^ 2 →
    M14BackwardLAction G p ≤ M14BackwardLAction G q ∧
      (M14BackwardLAction G q ≤ M14BackwardLAction G p → EqOn q.curve p.curve (Icc τ₁ τ₂)) := by
  dsimp only
  intro hpos hLip hshort
  let C := M14SqrtParameterInterval τ₁ τ₂
  let u := fun s => (lift (p.curve (s ^ 2))).2.val
  let z := fun s => (lift (q.curve (s ^ 2))).2.val
  let v := derivWithin u C
  let B := squareMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := squarePotentialCoefficient b θ x₀
  let DB := M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) B
  let DV := M08.spatialWithinFDeriv D (G.gaugeCover.spatial b) V
  have hab := Real.sqrt_lt_sqrt p.tau_nonneg p.tau_lt
  have hu := squareGauge_spatial_contDiffOn p b lift hCoordinates hM12 F heuler hU hlift hright
    hab le_rfl le_rfl (fun s hs => (hp s hs).1)
  have hv : ContinuousOn v C := hu.continuousOn_derivWithin (uniqueDiffOn_Icc hab) (by simp)
  have hvd (s : ℝ) (hs : s ∈ Ioo (Real.sqrt τ₁) (Real.sqrt τ₂)) : v s = deriv u s :=
    derivWithin_of_mem_nhds (Icc_mem_nhds hs.1 hs.2)
  obtain ⟨hz, hzd, hzLp⟩ := squarePath_gauge_derivative_memLp q b lift hM12 hlift hright
    hab le_rfl le_rfl (fun s hs => (hq s hs).1)
  have hB : ContDiffOn ℝ ∞ B (D ×ˢ (G.gaugeCover.spatial b : Set _)) :=
    squareMetricCoefficient_contDiffOn (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric
      (G.gaugeCover.metric b).smooth T x₀ (fun s hs => by
        rw [← hclock s hs]
        exact (θ s).property)
  have hV : ContDiffOn ℝ ∞ V (D ×ˢ (G.gaugeCover.spatial b : Set _)) :=
    squarePotentialCoefficient_contDiffOn b θ x₀ hM12 hθ
  have hsmall : C ×ˢ S ⊆ D ×ˢ (G.gaugeCover.spatial b : Set _) := prod_mono hsub hSU
  have hmomentum := squarePath_gauge_momentum_fixed_window p b lift x₀ hCoordinates hM12 F
    heuler hU hlift hright (fun s hs => (hp s hs).1) hsub θ hθ hclock v hvd
  have hpa := squarePath_gauge_action_eq p b lift x₀ hM12 θ hlift hright
    (fun s hs => (hp s hs).1) (fun s hs => hclock s (hsub hs))
  have hqa := squarePath_gauge_action_eq q b lift x₀ hM12 θ hlift hright
    (fun s hs => (hq s hs).1) (fun s hs => hclock s (hsub hs))
  have hpa' : (∫ s in Real.sqrt τ₁..Real.sqrt τ₂,
      B (s, u s) (v s) (v s) / 2 + V (s, u s)) = M14BackwardLAction G p := by
    rw [← hpa.2]
    apply intervalIntegral.integral_congr_Ioo_of_le hab.le
    intro s hs
    dsimp only
    rw [hvd s hs]
  have hstart : z (Real.sqrt τ₁) = u (Real.sqrt τ₁) := by
    dsimp only [z, u]
    rw [Real.sq_sqrt p.tau_nonneg, q.curve_start, p.curve_start]
  have hend : z (Real.sqrt τ₂) = u (Real.sqrt τ₂) := by
    dsimp only [z, u]
    rw [Real.sq_sqrt (p.tau_nonneg.trans p.tau_lt.le), q.curve_end, p.curve_end]
  have hcomp := quadratic_short_time_minimality hab.le hm hS K B V DB DV
    (hB.continuousOn.mono hsmall) (hV.continuousOn.mono hsmall)
    ((M08.spatialWithinFDeriv_contDiffOn hD (G.gaugeCover.spatial b).isOpen B hB).continuousOn.mono
      hsmall)
    ((M08.spatialWithinFDeriv_contDiffOn hD (G.gaugeCover.spatial b).isOpen V hV).continuousOn.mono
      hsmall)
    (fun s hs y hy => (M08.hasFDerivAt_spatialWithin (G.gaugeCover.spatial b).isOpen
      B hB (hsub hs) (hSU hy)).hasFDerivWithinAt)
    (fun s hs y hy => (M08.hasFDerivAt_spatialWithin (G.gaugeCover.spatial b).isOpen
      V hV (hsub hs) (hSU hy)).hasFDerivWithinAt)
    (fun s hs => (hLip s (hsub hs)).1)
    (fun s hs => (hLip s (hsub hs)).2.1)
    (fun s hs => (hLip s (hsub hs)).2.2)
    (fun z hz v w => by
      rcases z with ⟨s, y⟩
      dsimp only [B]
      rw [show y = (⟨y, hSU hz.2⟩ : G.gaugeCover.spatial b).val from rfl,
        squareMetricCoefficient_apply, squareMetricCoefficient_apply]
      exact ((G.gaugeCover.metric b).metric (T - s ^ 2)).symm _ v w)
    (fun z hz => hpos z ⟨hsub hz.1, hz.2⟩) u v hu.continuousOn hv
    (fun s hs => (hp s hs).2) hspeed
    (fun s hs => by
      rw [hvd s hs]
      exact (((hu s (Ioo_subset_Icc_self hs)).contDiffAt
        (Icc_mem_nhds hs.1 hs.2)).differentiableAt (by simp)).hasDerivAt)
    hmomentum hshort z (deriv z) hz (fun s hs => (hq s hs).2) hzd hzLp hstart hend hqa.1
  rw [hpa', hqa.2] at hcomp
  refine ⟨hcomp.1, ?_⟩
  intro haction t ht
  have hs : Real.sqrt t ∈ C := ⟨Real.sqrt_le_sqrt ht.1, Real.sqrt_le_sqrt ht.2⟩
  have heq := hcomp.2 haction hs
  have hsp : (lift (q.curve t)).2 = (lift (p.curve t)).2 := by
    apply Subtype.ext
    simpa only [z, u, Real.sq_sqrt (p.tau_nonneg.trans ht.1)] using heq
  have hqt : q.curve t ∈ U := by
    simpa only [Real.sq_sqrt (p.tau_nonneg.trans ht.1)] using (hq (Real.sqrt t) hs).1
  have hpt : p.curve t ∈ U := by
    simpa only [Real.sq_sqrt (p.tau_nonneg.trans ht.1)] using (hp (Real.sqrt t) hs).1
  have htime : (lift (q.curve t)).1 = (lift (p.curve t)).1 := Subtype.ext
    ((gaugeLift_time_eq q b lift hright ht hqt).trans
      (gaugeLift_time_eq p b lift hright ht hpt).symm)
  exact (hright _ hqt).symm.trans
    ((congrArg (G.gaugeCover.cylinder b).toSpacetime (Prod.ext htime hsp)).trans (hright _ hpt))

end PoincareConjecture.M14
