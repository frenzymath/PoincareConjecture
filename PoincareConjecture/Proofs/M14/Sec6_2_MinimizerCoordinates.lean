import PoincareConjecture.Proofs.M14.Mathlib.QuadraticMinimizerRegularity
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeAction










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




theorem minimizing_gaugeCoordinate_regularity
    (hM12 : GeneralizedRicciGaugeTheory.{u} n) (hmin : M14IsMinimizing p)
    {U : Set G.Point} (hU : IsOpen U)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift U)
    (hright : ∀ q ∈ U, (G.gaugeCover.cylinder b).toSpacetime (lift q) = q)
    {J : Set ℝ} (hJ : IsOpen J) (hJsub : J ⊆ Ioo τ₁ τ₂)
    (hsrc : ∀ t ∈ J, p.curve t ∈ U) {a c : ℝ} (hac : a < c) (hacJ : Icc a c ⊆ J) :
    let u := fun t => (lift (p.curve t)).2.val
    let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
    let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
    ContDiffOn ℝ ∞ u (Icc a c) ∧ ∀ t ∈ Icc a c,
      HasDerivWithinAt
        (fun s => M08.chartMomentumVector (B (s, u s)) (derivWithin u (Icc a c) s))
        (M08.chartForceVector (M08.spatialFDeriv B (t, u t))
          (M08.spatialFDeriv V (t, u t)) (derivWithin u (Icc a c) t)) (Icc a c) t := by
  let u := fun t => (lift (p.curve t)).2.val
  let B := backwardMetricCoefficient (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
  let V := backwardPotentialCoefficient b (fun t => (lift (p.curve t)).1) x₀
  let Ω := J ×ˢ (G.gaugeCover.spatial b : Set (EuclideanSpace ℝ (Fin n)))
  have hΩ : IsOpen Ω := hJ.prod (G.gaugeCover.spatial b).isOpen
  have hsub : Icc a c ×ˢ (G.gaugeCover.spatial b : Set _) ⊆ Ω :=
    fun _ hz => ⟨hacJ hz.1, hz.2⟩
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
  have hDB := M08.spatialFDeriv_contDiffOn hΩ B hB
  have hDV := M08.spatialFDeriv_contDiffOn hΩ V hV
  have hu : ContDiffOn ℝ 1 u (Icc a c) :=
    (gaugeLift_spatial_contDiffOn p b lift hlift hJsub hsrc).mono hacJ
  have ha : τ₁ < a := (hJsub (hacJ (left_mem_Icc.mpr hac.le))).1
  have hc : c < τ₂ := (hJsub (hacJ (right_mem_Icc.mpr hac.le))).2
  apply ODE.contDiffOn_of_quadratic_local_minima hac B V
    (M08.spatialFDeriv B) (M08.spatialFDeriv V) (hB.mono hsub) (hV.continuousOn.mono hsub)
    (hDB.mono hsub) (hDV.mono hsub)
  · exact fun z hz => M08.hasFDerivAt_spatial hΩ B hB (hsub hz)
  · exact fun z hz => M08.hasFDerivAt_spatial hΩ V hV (hsub hz)
  · exact fun z _ v w => backwardMetricCoefficient_symm
      (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀ z v w
  · exact fun z hz v hv => backwardMetricCoefficient_pos
      (G.gaugeCover.spatial b) (G.gaugeCover.metric b).metric T x₀
        (hpos z.1 (hacJ hz.1)) hz.2 v hv
  · exact hu
  · exact fun t _ => (lift (p.curve t)).2.property
  · intro η hη hsupp
    exact exists_quadratic_local_minimum p b lift η x₀ hM12 hmin hU hlift hright
      ha hac hc hη hsupp (fun t ht => hsrc t (hacJ ht))

end PoincareConjecture.M14
