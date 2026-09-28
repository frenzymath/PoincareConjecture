import PoincareConjecture.Proofs.M46.Sec16_1_LGeometry.Prop16_4_UniformRestart
import PoincareConjecture.Proofs.M14.Sec6_3_LocalEulerPath

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Topology Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem exists_gaugeEulerPath_uniform_restart_neighborhood
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (V₀ : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {T a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (s₀ : Icc a c)
    (htime : ∀ s ∈ Icc a c, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    let z₀ := (x₀.val, M08.chartMetricOperator W.flow T x₀ (s₀.val, x₀.val)
      (((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm V₀))
    ∃ l r : ℝ, a ≤ l ∧ l < r ∧ r ≤ c ∧ Icc l r ∈ 𝓝[Icc a c] s₀.val ∧
      ∃ rho : ℝ, 0 < rho ∧ ∀ᶠ s in 𝓝[Icc a c] s₀.val,
        s ∈ Icc l r ∧
        ∀ (t : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
          (x : G.gaugeCover.spatial b)
          (V : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t, x))),
        T - s ^ 2 = t.val →
        (x.val, M08.chartMetricOperator W.flow T x₀ (s, x.val)
          (((G.gaugeCover.metric b).spatialTangentEquiv t x).symm V)) ∈ ball z₀ rho →
        ∃ q₀ q₁ : G.Point, ∃ p : M14BackwardPath G T (l ^ 2) (r ^ 2) q₀ q₁,
          ∃ R : M14SquareRootPath G p,
          ∃ E : M14PullbackExtension G R.curve
            (M14SqrtParameterInterval (l ^ 2) (r ^ 2)) R.horizontal_velocity,
            (∀ w ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2), ∀ Z,
              M14SquareRootEulerResidual G R E w Z = 0) ∧
            R.curve s = (G.gaugeCover.cylinder b).toSpacetime (t, x) ∧
              HEq (R.horizontal_velocity s) V := by
  dsimp only
  let z₀ := (x₀.val, M08.chartMetricOperator W.flow T x₀ (s₀.val, x₀.val)
    (((G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀).symm V₀))
  have htarget (x : G.gaugeCover.spatial b) :
      x.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ x = x.val := by rw [extChartAt_coe]; rfl
    rw [← hval]
    apply (extChartAt (𝓡 n) x₀).map_source
    rw [extChartAt_source, (G.gaugeCover.spatial b).chartAt_source_eq_univ]
    exact mem_univ _
  obtain ⟨l, r, hlr, hal, hrc, hnear, rho, hrho, hrestart⟩ :=
    exists_closedChartEulerPhase_uniform_restart_neighborhood W.flow hM04 T x₀
      hac htime s₀ (z₀ := z₀) (htarget x₀)
  have hl : 0 ≤ l := ha.trans hal
  have hr : 0 ≤ r := hl.trans hlr.le
  have hC : M14SqrtParameterInterval (l ^ 2) (r ^ 2) = Icc l r := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hr]
  refine ⟨l, r, hal, hlr, hrc, hnear, rho, hrho, ?_⟩
  filter_upwards [hrestart] with s hs
  refine ⟨hs.1, ?_⟩
  intro t x V hclock hphaseNear
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t x
  let z := (x.val, M08.chartMetricOperator W.flow T x₀ (s, x.val) (j.symm V))
  obtain ⟨gamma, hgamma, hsmooth, hdata⟩ := hs.2 z hphaseNear
  have htime' : ∀ w ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2),
      T - w ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [hC]
    exact fun w hw => htime w ((Icc_subset_Icc hal hrc) hw)
  obtain ⟨beta, _, hclockBeta, hcoordBeta, p, R, E, _, hrec, hEuler, hvel⟩ :=
    M14.exists_gaugeEulerPath_of_phase hM04 hM12 b W t₀ x₀ (sq_nonneg l)
      ((sq_lt_sq₀ hl hr).mpr hlr) htime'
      (q := fun w => (gamma w).1) (P := fun w => (gamma w).2)
      (by simpa only [hC] using hsmooth.fst)
      (by rw [hC]; exact fun w hw => (hdata w hw).1)
      (by simpa only [hC, Prod.eta] using fun w hw => (hdata w hw).2)
  have hsC : s ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2) := hC ▸ hs.1
  have hbeta : beta s = (t, x) := by
    apply Prod.ext
    · exact Subtype.ext ((hclockBeta s hsC).trans hclock)
    · exact Subtype.ext ((hcoordBeta s hsC).trans (congrArg Prod.fst hgamma))
  have hvd : derivWithin (fun w => (gamma w).1) (Icc l r) s = j.symm V := by
    have hd₀ := (ContinuousLinearMap.fst ℝ (EuclideanSpace ℝ (Fin n))
      (EuclideanSpace ℝ (Fin n))).hasFDerivAt.comp_hasDerivWithinAt s (hdata s hs.1).2
    have hd := hd₀.derivWithin (uniqueDiffOn_Icc hlr s hs.1)
    change derivWithin (fun w => (gamma w).1) (Icc l r) s =
      Ring.inverse (M08.chartMetricOperator W.flow T x₀ (s, (gamma s).1))
        (gamma s).2 at hd
    rw [hgamma] at hd
    exact hd.trans (M08.inverse_operator_apply _
      (M08.chartMetricOperator_isUnit_of_target W.flow T x₀ (htarget x)) _)
  have hV := hvel s hsC
  rw [hC, hbeta, hvd, ContinuousLinearEquiv.apply_symm_apply] at hV
  exact ⟨_, _, p, R, E, hEuler,
    (hrec s hsC).trans (congrArg (G.gaugeCover.cylinder b).toSpacetime hbeta), hV⟩

end PoincareConjecture.Proofs.M46
