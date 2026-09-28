import PoincareConjecture.Proofs.M15.Thm8_10_DoublingTime
import PoincareConjecture.Proofs.M15.Thm1_34_LocalVolume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Restriction
import PoincareConjecture.Definitions.M15Noncollapsing










set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M15




theorem compact_completeBoundedCurvatureOn
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [CompactSpace M] {J S : Set ℝ}
    (F : RicciFlow n M J) (hS : IsCompact S) (hSJ : S ⊆ J) :
    CompleteBoundedCurvatureOn F S := by
  have hE : ContinuousOn
      (fun p : ℝ × M => ((F.connection p.1).curvatureTensorNorm p.2)^2)
      (J ×ˢ univ) := by
    simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using
      (M04.contMDiffOn_flow_curvatureDerivativeEnergy F 0).continuousOn
  have hN : ContinuousOn (fun p : ℝ × M => (F.connection p.1).curvatureTensorNorm p.2)
      (S ×ˢ univ) := by
    apply (hE.mono (prod_mono hSJ (subset_refl _))).sqrt.congr
    intro p hp
    exact (Real.sqrt_sq (show 0 ≤ (F.connection p.1).curvatureTensorNorm p.2 from
      Real.sqrt_nonneg _)).symm
  obtain ⟨K, hK⟩ := (hS.prod (isCompact_univ : IsCompact (univ : Set M))).bddAbove_image hN
  constructor
  · intro t ht
    unfold MetricComplete
    infer_instance
  · refine ⟨max K 0, le_max_right _ _, ?_⟩
    intro t ht q
    rw [abs_of_nonneg (show 0 ≤ (F.connection t).curvatureTensorNorm q from Real.sqrt_nonneg _)]
    exact (hK (mem_image_of_mem _ (show (t, q) ∈ S ×ˢ univ from
      ⟨ht, mem_univ q⟩))).trans (le_max_left _ _)





theorem compact_estimate_of_connected {omega T0 kappa : ℝ}
    (hconnected : ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
      [CompactSpace M] [ConnectedSpace M]
      (T : ℝ) (F : RicciFlow 3 M (Icc 0 T))
      (D : M15CompactTheorem810Data M T F omega T0),
      M15CompactTheorem810Estimate D kappa) :
    ∀ (M : Type u) [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [T3Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M]
      [CompactSpace M] (T : ℝ) (F : RicciFlow 3 M (Icc 0 T))
      (D : M15CompactTheorem810Data M T F omega T0),
      M15CompactTheorem810Estimate D kappa := by
  intro M _ _ _ _ _ _ _ _ T F D
  let U := Poincare.connectedComponentOpens (EuclideanSpace ℝ (Fin 3)) D.p
  let : CompactSpace U := isCompact_iff_compactSpace.mp
    (show IsCompact (U : Set M) from isClosed_connectedComponent.isCompact)
  let pU : U := ⟨D.p, mem_connectedComponent⟩
  let FU := F.restrictComponent D.p
  have hvolume (t : ℝ) (q : U) (r : ℝ) :
      calibratedMetricVolume (FU.metric t) ((FU.metric t).ball q r) =
        calibratedMetricVolume (F.metric t) ((F.metric t).ball q.val r) := by
    rw [calibratedMetricVolume_eq_volumeMeasure, calibratedMetricVolume_eq_volumeMeasure]
    exact F.restrictComponent_volumeMeasure_ball D.p t q r
  let DU : M15CompactTheorem810Data U T FU omega T0 := {
    T_pos := D.T_pos
    T_le_T₀ := D.T_le_T₀
    omega_pos := D.omega_pos
    T₀_pos := D.T₀_pos
    initial_curvature_bound := fun q => by
      change |((F.restrictComponent D.p).connection 0).curvatureTensorNorm q| ≤ 1
      rw [F.restrictComponent_curvatureTensorNorm D.p 0 q]
      exact D.initial_curvature_bound q.val
    initial_unit_ball_volume := fun q => by
      rw [hvolume]
      exact D.initial_unit_ball_volume q.val
    t₀ := D.t₀
    t₀_mem := D.t₀_mem
    t₀_nonneg := D.t₀_nonneg
    t₀_le_T := D.t₀_le_T
    p := pU
    r := D.r
    radius_pos := D.radius_pos
    radius_sq_le_t₀ := D.radius_sq_le_t₀
    time_window := D.time_window
    curvature_bound := fun s hs q hq => by
      have hq' : q.val ∈ (F.metric D.t₀).ball D.p D.r := by
        change (F.metric D.t₀).edist D.p q.val < ENNReal.ofReal D.r
        change (FU.metric D.t₀).edist pU q < ENNReal.ofReal D.r at hq
        simpa only [FU, RicciFlow.restrictComponent_edist, pU] using hq
      change |((F.restrictComponent D.p).connection s).curvatureTensorNorm q| ≤ D.r⁻¹ ^ 2
      rw [F.restrictComponent_curvatureTensorNorm D.p s q]
      exact D.curvature_bound s hs q.val hq'
  }
  have h := hconnected U T FU DU
  change ENNReal.ofReal (kappa * D.r ^ 3) ≤
    calibratedMetricVolume (FU.metric D.t₀) ((FU.metric D.t₀).ball pU D.r) at h
  rw [hvolume] at h
  exact h

end PoincareConjecture.Proofs.M15
