import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_GaugePhaseCoordinates
import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_UniformGaugeRestart
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Bundle Metric
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}





theorem exists_actualPhase_uniform_restart
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T s : ℝ} (hT : T ∈ I.domain) (hs : 0 < s)
    (z₀ : TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal)
    (hclock : G.spacetime.timeFunction z₀.proj = T - s ^ 2) :
    ∃ l r : ℝ, 0 < l ∧ l < s ∧ s ≤ r ∧
      Icc l r ∈ 𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s ∧
      ∀ᶠ z in 𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s ×ˢ 𝓝 z₀,
        z.1 ∈ Icc l r ∧
        (G.spacetime.timeFunction z.2.proj = T - z.1 ^ 2 →
          ∃ q₀ q₁ : G.Point, ∃ p : M14BackwardPath G T (l ^ 2) (r ^ 2) q₀ q₁,
            ∃ R : M14SquareRootPath G p,
            ∃ E : M14PullbackExtension G R.curve
              (M14SqrtParameterInterval (l ^ 2) (r ^ 2)) R.horizontal_velocity,
              (∀ w ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2), ∀ V,
                M14SquareRootEulerResidual G R E w V = 0) ∧
              R.curve z.1 = z.2.proj ∧ HEq (R.horizontal_velocity z.1) z.2.2) := by
  obtain ⟨b, U, lift, hU, hzU, hlift, hrec, htimeLift⟩ :=
    M14.exists_smooth_gauge_lift G z₀.proj
  let S : Set (TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal) := {z | z.proj ∈ U}
  have hS : IsOpen S := hU.preimage (FiberBundle.continuous_proj _ _)
  have hzS : z₀ ∈ S := hzU
  obtain ⟨v, hv, hvelocity⟩ := exists_continuous_gaugeVelocity_coordinates b lift hlift hrec
  let t₀ := (lift z₀.proj).1
  let x₀ := (lift z₀.proj).2
  let V₀ := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀ (v z₀)
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨W⟩ := M14.ordinaryGaugeWitness_nonempty b hCoordinates
  have htime₀ : T - s ^ 2 = t₀.val := hclock.symm.trans (htimeLift z₀.proj hzU).symm
  obtain ⟨a, c, ha, has, hsc, htime, hwindow⟩ :=
    M14.exists_gauge_positive_squareClock_window b t₀ x₀ hT hs htime₀
  obtain ⟨l, r, hal, _, _, hnear, rho, hrho, hrestart⟩ :=
    exists_gaugeEulerPath_uniform_restart_neighborhood hM04 hM12 b W t₀ x₀ V₀
      ha.le (has.trans_le hsc) ⟨s, has.le, hsc⟩ htime
  have hls : l < s := M14.left_lt_of_Icc_mem_nhdsWithin has hsc hnear
  have hsr : s ≤ r :=
    (mem_of_mem_nhdsWithin (show s ∈ Icc a c from ⟨has.le, hsc⟩) hnear).2
  let f := fun z : ℝ × TotalSpace (EuclideanSpace ℝ (Fin n)) G.Horizontal =>
    ((lift z.2.proj).2.val,
      M08.chartMetricOperator W.flow T x₀ (z.1, (lift z.2.proj).2.val) (v z.2))
  have hf : ContinuousOn f (Icc a c ×ˢ S) :=
    gaugeMomentum_coordinates_continuousOn b W lift hlift v hv T x₀ htime
  have hfnear : {z | f z ∈ ball (f (s, z₀)) rho} ∈ 𝓝[Icc a c ×ˢ S] (s, z₀) :=
    (hf (s, z₀) ⟨⟨has.le, hsc⟩, hzS⟩).preimage_mem_nhdsWithin
      (ball_mem_nhds _ hrho)
  rw [nhdsWithin_prod_eq, nhdsWithin_eq_nhds.mpr (hS.mem_nhds hzS)] at hfnear
  have hfilter : 𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s ≤ 𝓝[Icc a c] s :=
    nhdsWithin_le_of_mem hwindow
  have hfnear' := (Filter.prod_mono hfilter (le_refl (𝓝 z₀))) hfnear
  have hrestart' := hrestart.filter_mono hfilter
  have hSnear : ∀ᶠ z in 𝓝 z₀, z ∈ S := hS.mem_nhds hzS
  refine ⟨l, r, ha.trans_le hal, hls, hsr, nhdsWithin_le_of_mem hwindow hnear, ?_⟩
  filter_upwards [hrestart'.prod_inl (𝓝 z₀), hfnear',
    hSnear.prod_inr (𝓝[{w | 0 ≤ w ∧ T - w ^ 2 ∈ I.domain}] s)]
    with z hzRestart hzNear hzS'
  refine ⟨hzRestart.1, ?_⟩
  intro hzClock
  let t := (lift z.2.proj).1
  let x := (lift z.2.proj).2
  let V := (G.gaugeCover.metric b).spatialTangentEquiv t x (v z.2)
  have htClock : T - z.1 ^ 2 = t.val :=
    hzClock.symm.trans (htimeLift z.2.proj hzS').symm
  have hphaseNear : (x.val, M08.chartMetricOperator W.flow T x₀ (z.1, x.val)
      (((G.gaugeCover.metric b).spatialTangentEquiv t x).symm V)) ∈
      ball (x₀.val, M08.chartMetricOperator W.flow T x₀ (s, x₀.val)
        (((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm V₀)) rho := by
    simpa only [V, V₀, ContinuousLinearEquiv.symm_apply_apply] using hzNear
  obtain ⟨q₀, q₁, p, R, E, hEuler, hpoint, hvel⟩ :=
    hzRestart.2 t x V htClock hphaseNear
  exact ⟨q₀, q₁, p, R, E, hEuler, hpoint.trans (hrec z.2.proj hzS'),
    hvel.trans (hvelocity z.2 hzS').symm⟩

end PoincareConjecture.Proofs.M46
