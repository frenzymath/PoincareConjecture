import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.Unnormalized.Interior
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Ancient.Preservation
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Compactness.Assembly











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture.AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance inheritanceCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)
  (G : AncientPointedGeometricConvergence C (fun k t => (K k).flow.metric (t - 1)) p 1)



theorem interiorLimit_nonnegativeCurvatureOperator :
    ∀ t : ℝ, t < 1 → ∀ x : G.limitCarrier.carrier,
      (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  let F (k : ℕ) : RicciFlow 3 (C k).carrier ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (K k).flow.bufferedExpandingFlow 1
  apply G.nonnegativeCurvatureOperator_of_eventually F (by norm_num) ?_ ?_
  · intro a b hb
    exact Eventually.of_forall fun k t ht => by
      change t - 1 ≤ 0
      linarith [ht.2]
  · intro t ht
    change t < 1 at ht
    exact Eventually.of_forall fun k x =>
      (K k).nonnegative_curvature_operator (t - 1) (by linarith) x



theorem interiorLimit_complete
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ) (hkappa : ∀ k, (K k).kappa = κ)
    (hcontrol : ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
      ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) r,
        |((K k).flow.connection t).curvatureTensorNorm x| ≤ B)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric 0)) :
    ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t) := by
  intro t ht
  obtain ⟨a, b, ha, hb, hb1, htw⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_singleton (singleton_subset_iff.mpr ht)
  let F (k : ℕ) : RicciFlow 3 (C k).carrier ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (K k).flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo a b ⊆ (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro u hu
    change u - 1 ≤ 0
    linarith [hu.2]
  have hselected : ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
      ∀ k t, t ≤ 0 → ∀ x ∈ ((K (G.subsequence k)).flow.metric 0).ball (p (G.subsequence k)) r,
        |((K (G.subsequence k)).flow.connection t).curvatureTensorNorm x| ≤ B := by
    intro r hr
    obtain ⟨B, hB, hbound⟩ := hcontrol r hr
    exact ⟨B, hB, fun k => hbound (G.subsequence k)⟩
  let H := compactnessHypotheses (fun k => C (G.subsequence k))
    (fun k => K (G.subsequence k)) (fun k => p (G.subsequence k)) P
    hκ (fun k => hkappa (G.subsequence k)) hselected ha hb hb1.le
  let W : PointedGeometricConvergence H.sequence :=
    G.window F (ha.trans hb) hb1.le 0 hsub
  exact W.complete_interior hcomplete t (htw (mem_singleton t))



theorem exists_complete_nonnegative_interior_geometric_limit
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hκ : 0 < κ) (hkappa : ∀ k, (K k).kappa = κ)
    (hcontrol : ∀ r : ℝ, 0 < r → ∃ B : ℝ, 0 ≤ B ∧
      ∀ k t, t ≤ 0 → ∀ x ∈ ((K k).flow.metric 0).ball (p k) r,
        |((K k).flow.connection t).curvatureTensorNorm x| ≤ B) :
    ∃ G : AncientPointedGeometricConvergence C (fun k t => (K k).flow.metric (t - 1)) p 1,
      (∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t)) ∧
      ∀ t : ℝ, t < 1 → ∀ x : G.limitCarrier.carrier,
        (G.limitFlow.connection t).NonnegativeCurvatureOperator x := by
  obtain ⟨G, hG⟩ := exists_complete_interior_geometric_limit C K p P hκ hkappa hcontrol
  exact ⟨G, interiorLimit_complete C K p G P hκ hkappa hcontrol hG,
    interiorLimit_nonnegativeCurvatureOperator C K p G⟩

end PoincareConjecture.AncientKappaSequence
