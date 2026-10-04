import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Unnormalized.Noncollapse
import PoincareLib.Geometry.RicciFlow.AncientKappa.Compactness.Unnormalized.Flatness
import PoincareLib.Geometry.RicciFlow.Compactness.Convergence.Volume.Convergence

/-!
# Volume bounds on the retained flat interior limit

Interior ball-volume convergence preserves an eventual upper bound. If the
source base scalar tends to zero, flatness makes every parabolic curvature
condition automatic, giving the original kappa lower bound at every radius.

Reference: Morgan--Tian, Lemma 9.65 and Claim 9.66, pp. 225-227;
Kleiner--Lott, Appendix E, Corollary E.2, pp. 2848-2849.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareMT.AncientKappaSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

local instance volumeCarrierConnected (D : FlowCarrier 3) : ConnectedSpace D.carrier :=
  connectedSpace_iff_univ.mpr D.connected

variable (C : ℕ → FlowCarrier.{0} 3)
  (K : ∀ k, AncientKappaSolution 3 (C k).carrier) (p : ∀ k, (C k).carrier)
  (G : AncientPointedGeometricConvergence C (fun k t => (K k).flow.metric (t - 1)) p 1)

/-- An eventual source ball-volume upper bound passes to a complete interior
slice of the same selected limit. -/
theorem interiorLimit_ball_volume_le
    {s r : ℝ} (hs : s < 1) (hr : 0 < r)
    (hcomplete : G.limitCarrier.metricComplete (G.limitFlow.metric s))
    (v : ℝ≥0∞)
    (hvolume : ∀ᶠ k in atTop, calibratedMetricVolume ((K k).flow.metric (s - 1))
      (((K k).flow.metric (s - 1)).ball (p k) r) ≤ v) :
    calibratedMetricVolume (G.limitFlow.metric s) ((G.limitFlow.metric s).ball G.base r) ≤ v := by
  obtain ⟨a, b, ha, hb, hb1, hsw⟩ := exists_ancient_window_of_isCompact
    (by norm_num : (0 : ℝ) < 1) isCompact_singleton (singleton_subset_iff.mpr hs)
  let F (k : ℕ) : RicciFlow 3 (C k).carrier ((fun t : ℝ => t - 1) ⁻¹' Iic 0) :=
    (K k).flow.bufferedExpandingFlow 1
  have hsub (k : ℕ) : Ioo a b ⊆ (fun t : ℝ => t - 1) ⁻¹' Iic 0 := by
    intro t ht
    change t - 1 ≤ 0
    linarith [ht.2]
  let W := G.window F (ha.trans hb) hb1.le 0 hsub
  have hconv := W.tendsto_riemannianBallVolume ⟨ha, hb⟩
    (hsw (mem_singleton s)) hr hcomplete
  change Tendsto (fun k => ((K (G.subsequence (k + 0))).flow.metric (s - 1)).volumeMeasure
      (((K (G.subsequence (k + 0))).flow.metric (s - 1)).ball (p (G.subsequence (k + 0))) r))
    atTop (𝓝 ((G.limitFlow.metric s).volumeMeasure ((G.limitFlow.metric s).ball G.base r))) at hconv
  rw [calibratedMetricVolume_eq_volumeMeasure]
  apply le_of_tendsto hconv
  filter_upwards [G.subsequence_strictMono.tendsto_atTop.eventually hvolume] with k hk
  simpa only [Nat.add_zero, calibratedMetricVolume_eq_volumeMeasure] using hk

/-- Flatness of the retained limit upgrades its original parabolic kappa
bound to an all-radius volume lower bound at every interior slice. -/
theorem interiorLimit_ball_volume_ge_of_base_scalar_tendsto_zero
    (P : M23NormalizedKappaCompactnessPredecessors)
    {κ : ℝ} (hkappa : ∀ k, (K k).kappa = κ)
    (hcomplete : ∀ t : ℝ, t < 1 → G.limitCarrier.metricComplete (G.limitFlow.metric t))
    (hscalar : Tendsto (fun k => ((K k).flow.connection 0).scalarCurvature (p k))
      atTop (𝓝 0))
    {s r : ℝ} (hs : s < 1) (q : G.limitCarrier.carrier) (hr : 0 < r) :
    ENNReal.ofReal (κ * r ^ 3) ≤ calibratedMetricVolume (G.limitFlow.metric s)
      ((G.limitFlow.metric s).ball q r) := by
  apply interiorLimit_noncollapsed_ball C K p G hkappa hcomplete hs q hr
  intro t ht x _
  rw [interiorLimit_flat_of_base_scalar_tendsto_zero C K p G P hscalar t
    (ht.2.trans_lt hs) x, abs_zero]
  exact sq_nonneg _

end PoincareMT.AncientKappaSequence
