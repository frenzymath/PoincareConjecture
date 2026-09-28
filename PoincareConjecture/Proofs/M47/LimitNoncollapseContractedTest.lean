import PoincareConjecture.Proofs.M47.LimitNoncollapseTestParameters
import PoincareConjecture.Proofs.M47.LimitNoncollapseUniformCurvature
import PoincareConjecture.Proofs.M47.LimitNoncollapseFiniteSlabs











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology ENNReal

universe u

namespace PoincareConjecture.M47

variable {S : GeneralizedBlowupSequence.{u}} {H : ENNReal}
  (G : GeneralizedBlowupConvergence S (blowupBackwardInterval H))

private local instance : TopologicalSpace G.limit.carrier.carrier :=
  G.limit.carrier.topologicalSpace
private local instance : MeasurableSpace G.limit.carrier.carrier :=
  G.limit.carrier.measurableSpace
private local instance : BorelSpace G.limit.carrier.carrier := G.limit.carrier.borelSpace
private local instance : ChartedSpace (EuclideanSpace ℝ (Fin 3)) G.limit.carrier.carrier :=
  G.limit.carrier.chartedSpace
private local instance : IsManifold (𝓡 3) ∞ G.limit.carrier.carrier := G.limit.carrier.isManifold
private local instance : T3Space G.limit.carrier.carrier := G.limit.carrier.t3Space
private local instance : SecondCountableTopology G.limit.carrier.carrier :=
  G.limit.carrier.secondCountable
private local instance : ConnectedSpace G.limit.carrier.carrier := G.limit.connectedSpace




theorem limitNoncollapse_contracted_test_volume
    (P : M47Predecessors.{u}) (t : ℝ) (ht : t ∈ blowupBackwardInterval H)
    (p : G.limit.carrier.carrier) {r rho R lambda kappa r0 : ℝ}
    (hr : 0 < r) (hrho : 0 < rho) (hsmall : rho < r)
    (hR : 0 < R) (hRr : R < r) (hlambda : 0 < lambda) (hlambda_lt : lambda < 1)
    (hbuffer : rho / lambda < R) (hr0 : 0 < r0)
    (hslabs : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < H →
      ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in atTop,
        Nonempty (M30FiniteHorizonSlab S k A T kappa r0))
    (htime : Ioc (t - r ^ 2) t ⊆ blowupBackwardInterval H)
    (hcurv : ∀ s ∈ Ioc (t - r ^ 2) t, ∀ x ∈ (G.limit.flow.metric t).ball p r,
      |(G.limit.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ENNReal.ofReal (kappa * lambda ^ 3 * rho ^ 3) ≤
      calibratedMetricVolume (G.limit.flow.metric t) ((G.limit.flow.metric t).ball p r) := by
  classical
  let g := G.limit.flow.metric t
  let Ktime := Icc (t - rho ^ 2) t
  let Kspace := closure (g.ball p R)
  have hKtime : IsCompact Ktime := isCompact_Icc
  have hsub : Ktime ⊆ Ioc (t - r ^ 2) t :=
    limitNoncollapse_shrunk_closed_time_subset hrho hsmall
  have hKJ : Ktime ⊆ blowupBackwardInterval H := hsub.trans htime
  have htop : t ∈ Ktime := ⟨sub_le_self _ (sq_nonneg rho), le_rfl⟩
  have hbottom : t - rho ^ 2 ∈ Ktime := ⟨le_rfl, sub_le_self _ (sq_nonneg rho)⟩
  have hKspace : IsCompact Kspace :=
    Proofs.M09.isCompact_closure_metric_ball g (G.limit.complete t ht) p R
  have hspace : Kspace ⊆ g.ball p r := limitNoncollapse_closure_ball_subset g p hr hRr
  have hcaptured : g.ball p (rho / lambda) ⊆ Kspace := by
    intro x hx
    exact subset_closure (hx.trans_le (ENNReal.ofReal_le_ofReal hbuffer.le))
  obtain ⟨T, hT, hTH, hKT⟩ :=
    limitNoncollapse_exists_finite_test_horizon ht.1 hrho (hKJ hbottom)
  have hsource := limitNoncollapse_eventually_source_noncollapsed P G hT hTH
    (hslabs T hT hTH) p hKtime hKT
  have hmetric := limitNoncollapse_generalized_compact_tangent_comparison G hKspace
    t ht hlambda hlambda_lt
  have hthreshold : r⁻¹ ^ 2 < rho⁻¹ ^ 2 := by
    have hinv : r⁻¹ < rho⁻¹ := by
      simpa only [one_div] using (one_div_lt_one_div_of_lt hrho hsmall)
    nlinarith [inv_pos.mpr hr, inv_pos.mpr hrho]
  have hcurvature := limitNoncollapse_generalized_compact_curvature_lt G P hKtime hKJ
    hKspace (B := rho⁻¹ ^ 2) (fun s hs x hx =>
      ((le_abs_self _).trans (hcurv s (hsub hs) x (hspace hx))).trans_lt hthreshold)
  obtain ⟨k, hnc, hm, hK, hcut⟩ :=
    (hsource.and (hmetric.and (hcurvature.and
      (limitNoncollapse_eventually_physical_radius G rho hr0)))).exists
  let e := G.embedding k
  let Q := S.scale (G.subsequence k)
  let hs : t ∈ Icc (-G.exhaustion.time k) 0 := hnc.1 htop
  have hQ : 0 < Q := e.scale_pos
  obtain ⟨hcapture, hvolume⟩ := limitNoncollapse_physical_capture_and_volume e
    (G.exhaustion.space_open k) g p t hs hR hlambda hbuffer hKspace hm.1
    (fun x hx v => (hm.2.2 x hx v hs).1)
    (fun x hx v => (hm.2.2 x hx v hs).2)
  have hrange : MapsTo (fun s => t + Q * s)
      (Icc (-(rho / Real.sqrt Q) ^ 2) 0) (Icc (-G.exhaustion.time k) 0) :=
    (limitNoncollapse_physical_time_range hQ t rho).mono (Subset.refl _) hK.1
  have hball : ((S.flow (G.subsequence k)).metric
      ((S.base (G.subsequence k)).1 + t / Q)).ball (e.forward t hs p)
      (rho / Real.sqrt Q) ⊆ e.forward t hs '' G.exhaustion.space k :=
    hcapture.trans (image_mono (hcaptured.trans hm.1))
  have hphysical : ∀ s (hsk : s ∈ Icc (-(rho / Real.sqrt Q) ^ 2) 0),
      ∀ x ∈ ((S.flow (G.subsequence k)).metric
        ((S.base (G.subsequence k)).1 + t / Q)).ball (e.forward t hs p)
        (rho / Real.sqrt Q),
        |(S.flow (G.subsequence k)).curvatureNorm
          (e.pointMap (t + Q * s) (hrange hsk) (e.inverse t hs x))| ≤
          (rho / Real.sqrt Q)⁻¹ ^ 2 := by
    intro s hsk x hx
    obtain ⟨y, hy, heq⟩ := hcapture hx
    have hyK : y ∈ Kspace := hcaptured hy
    have hinverse : e.inverse t hs x = y := by
      rw [← heq]
      exact e.left_inverse t hs (hm.1 hyK)
    apply limitNoncollapse_physical_curvature_bound hQ
    rw [hinverse]
    have hn : 0 ≤ (S.flow (G.subsequence k)).curvatureNorm
        (e.pointMap (t + Q * s) (hrange hsk) y) := Real.sqrt_nonneg _
    rw [abs_of_nonneg hn]
    exact (hK.2.2 (t + Q * s) (limitNoncollapse_physical_time_range hQ t rho hsk)
      (hrange hsk) y hyK).le
  have hlower := limitNoncollapse_volume_of_recentered_test e (G.exhaustion.space_open k)
    t hs (e.forward t hs p) (div_pos hrho (Real.sqrt_pos.mpr hQ)) hcut
    (hnc.2.2 t htop hs) hrange hball hphysical
  have hnormalized := limitNoncollapse_cancel_physical_volume hQ hlambda hlower hvolume
  apply hnormalized.trans
  exact measure_mono (fun x hx => hx.trans_le (ENNReal.ofReal_le_ofReal hRr.le))

end PoincareConjecture.M47
