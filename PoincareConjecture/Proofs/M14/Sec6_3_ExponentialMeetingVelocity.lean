import PoincareConjecture.Proofs.M14.Sec6_3_EndpointCostHessian
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialPrefixMomentum
import PoincareConjecture.Proofs.M14.Sec6_3_ExponentialLineKernel
import PoincareConjecture.Proofs.M14.Sec6_3_MeetingMetric










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {T : ℝ} {x : G.Point}




theorem exponential_meetingVelocity_deriv_eq_zero
    (hCoordinates : M12MetricPredecessors.{0} n)
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (E : M14ExponentialFamily G T x) (Z W : G.Horizontal x)
    {b c : ℝ} (hb : (Z, b) ∈ E.domain) (hc : c ∈ Ioo 0 b)
    (hmin : M14IsMinimizing (E.path Z b hb (hc.1.trans hc.2)))
    (hZ : (Z, c) ∈ E.domain) (hker : E.differential Z c hZ W = 0)
    (j : G.gaugeCover.index)
    (lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
      G.gaugeCover.spatial j) {V : Set G.Point} (hV : IsOpen V)
    (hlift : ContMDiffOn (spacetimeModel n) (spacetimeModel n) ∞ lift V)
    (hright : ∀ q ∈ V, (G.gaugeCover.cylinder j).toSpacetime (lift q) = q)
    (hcenter : E.gamma Z c ∈ V) :
    deriv (fun r : ℝ => deriv (fun s => (lift (E.gamma (Z + r • W) s)).2.val) c) 0 = 0 := by
  obtain ⟨U, hU, hzero, hsurv, ⟨D⟩⟩ :=
    exists_exponentialLine_endpointFamily hM04 hM12 E Z W hb hc j lift hV hlift hright hcenter
  let f := fun z : ℝ × ℝ => E.gamma (Z + z.2 • W) z.1
  let ξ := fun r : ℝ => deriv (fun s => (lift (f (s, r))).2.val) c
  let t₀ := (lift (f (c, 0))).1
  let q₀ := (lift (f (c, 0))).2
  let g := fun y => Proofs.M11.ordinaryChartMetric (G.gaugeCover.metric j).metric q₀ (t₀.val, y)
  have hlift₀ := (hlift _ hcenter).contMDiffAt (hV.mem_nhds hcenter)
  have hliftF : ContMDiffAt (spacetimeModel n) (spacetimeModel n) ∞ lift
      (E.gamma (Z + (0 : ℝ) • W) c) := by
    simpa only [zero_smul, add_zero] using hlift₀
  have hξ : ContDiffAt ℝ ∞ ξ 0 :=
    (exponentialLine_gauge_coordinate_velocity_contDiffAt E Z W hU hsurv hc hzero j lift hliftF).2
  have ha0 := exponentialLine_coordinate_deriv_eq_zero E Z W hU hzero hsurv hc hZ hker j lift hlift₀
  have hprefix₀ := exponential_prefixAction_fderiv_eventually hCoordinates hM12 E Z W hU hsurv hc
    j lift D hV hlift hright hcenter
  have hprefix : ∀ᶠ r in 𝓝 (0 : ℝ), ∀ d : ℝ × EuclideanSpace ℝ (Fin n),
      fderiv ℝ D.prefixAction (r, (lift (f (c, r))).2.val) d =
        g (lift (f (c, r))).2.val (ξ r) d.2 := by
    filter_upwards [hprefix₀] with r hr
    intro d
    exact (hr d).trans (ordinaryChartMetric_openSubset_apply (G.gaugeCover.spatial j)
      (G.gaugeCover.metric j).metric q₀ (lift (f (c, r))).2 t₀.val (ξ r) d.2).symm
  have hpos (v : EuclideanSpace ℝ (Fin n)) (hv : v ≠ 0) : 0 < g q₀.val v v := by
    rw [show g q₀.val v v = ((G.gaugeCover.metric j).metric t₀.val).inner q₀ v v from
      ordinaryChartMetric_openSubset_apply (G.gaugeCover.spatial j)
        (G.gaugeCover.metric j).metric q₀ q₀ t₀.val v v]
    exact ((G.gaugeCover.metric j).metric t₀.val).pos q₀ v hv
  let m := E.path Z b hb (hc.1.trans hc.2)
  have heq : EqOn (fun t => f (Real.sqrt t, 0)) m.curve (Icc 0 (b ^ 2)) := by
    intro t ht
    simpa only [f, zero_smul, add_zero] using (E.path_coherent Z b hb (hc.1.trans hc.2) t ht).symm
  exact D.meetingVelocity_deriv_eq_zero hM12 hc m hmin heq
    (fun r _ => E.gamma_at_zero (Z + r • W))
    (by simp only [zero_smul, add_zero]) ξ g hξ (meetingMetric_contDiffAt j t₀ q₀) hpos ha0 hprefix

end PoincareConjecture.M14
