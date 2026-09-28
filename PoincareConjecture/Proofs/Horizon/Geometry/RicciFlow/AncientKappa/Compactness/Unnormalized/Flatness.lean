import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Unnormalized.Inheritance
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Convergence.Curvature
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Operator.SectionalBounds

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance flatnessCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)
  (G : AncientPointedGeometricConvergence C (fun k t => (K k).flow.metric (t - 1)) p 1)

theorem interiorLimit_base_curvatureTensorNorm_eq_zero
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hscalar : Tendsto (fun k => ((K k).flow.connection 0).scalarCurvature (p k))
      atTop (𝓝 0)) (s : ℝ) (hs : s < 1) :
    (G.limitFlow.connection s).curvatureTensorNorm G.base = 0 := by
  obtain ⟨a, b, ha, hb, hb1, hsw⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_singleton (singleton_subset_iff.mpr hs)
  let Fseq (k : ℕ) : RicciFlow 3 (C k).carrier
      ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (K k).flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo a b ⊆ (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window Fseq (ha.trans hb) hb1.le 0 (fun k => hsub (G.subsequence (k + 0)))
  have hconv := W.tendsto_curvatureTensorNorm s (hsw (mem_singleton s)) G.base
  change Tendsto (fun k => ((K (G.subsequence (k + 0))).flow.connection (s - 1)).curvatureTensorNorm
      (G.embedding (k + 0) G.base)) atTop
    (𝓝 ((G.limitFlow.connection s).curvatureTensorNorm G.base)) at hconv
  simp only [Nat.add_zero, G.base_preserving] at hconv
  apply le_antisymm ?_ (Real.sqrt_nonneg _)
  apply le_of_tendsto_of_tendsto hconv (hscalar.comp G.subsequence_strictMono.tendsto_atTop)
  exact Eventually.of_forall fun k => P.past_norm_le_scalar (C (G.subsequence k)).carrier
    (K (G.subsequence k)) (s - 1) 0 (by linarith) le_rfl (p (G.subsequence k))

theorem interiorLimit_flat_of_base_scalar_tendsto_zero
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hscalar : Tendsto (fun k => ((K k).flow.connection 0).scalarCurvature (p k))
      atTop (𝓝 0)) :
    ∀ t : ℝ, t < 1 → ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).curvatureTensorNorm x = 0 := by
  have hop := interiorLimit_nonnegativeCurvatureOperator C K p G
  have hbase (t : ℝ) (ht : t < 1) :
      (G.limitFlow.connection t).scalarCurvature G.base = 0 := by
    have hnorm := interiorLimit_base_curvatureTensorNorm_eq_zero C K p G P hscalar t ht
    have hbound := (G.limitFlow.connection t).abs_scalarCurvature_le_curvatureTensorNorm G.base
    rw [hnorm, mul_zero] at hbound
    exact abs_eq_zero.mp (le_antisymm hbound (abs_nonneg _))
  intro t ht x
  have hshift : (fun s : ℝ => s + (t - 1)) '' Icc 0 1 ⊆ Iio 1 := by
    rintro _ ⟨s, hs, rfl⟩
    change s + (t - 1) < 1
    linarith [hs.2]
  have hne : (Icc (0 : ℝ) 1).Nontrivial :=
    ⟨0, by norm_num, 1, by norm_num, by norm_num⟩
  let F := G.limitFlow.translate (t - 1) hshift ordConnected_Icc hne
  have htime : (1 : ℝ) + (t - 1) = t := by ring
  have hsec : ∀ s ∈ Icc 0 1, (F.connection s).NonnegativeSectionalCurvature := by
    intro s hs y v w
    exact (G.limitFlow.connection (s + (t - 1))).curvatureTensor_self_nonneg_of_nonnegative_curvatureOperator
      y (hop _ (by linarith [hs.2]) y) v w
  have hzero : (F.connection 1).scalarCurvature G.base = 0 := by
    change (G.limitFlow.connection (1 + (t - 1))).scalarCurvature G.base = 0
    rw [htime]
    exact hbase t ht
  have h := P.scalar_zero_rigidity G.limitCarrier.carrier 1 (by norm_num)
    F hsec G.base hzero 1 (by norm_num) x
  change (G.limitFlow.connection (1 + (t - 1))).curvatureTensorNorm x = 0 at h
  rwa [htime] at h

end PoincareConjecture.AncientKappaSequence
