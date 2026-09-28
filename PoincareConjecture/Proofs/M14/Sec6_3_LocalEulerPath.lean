import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerJointFamily
import PoincareConjecture.Proofs.M14.Sec6_3_PhasePath
import PoincareConjecture.Proofs.M14.Sec6_3_SquareClockWindows










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_gaugeEulerPath_through_velocity
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (V : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {T a c : ℝ} (ha : 0 ≤ a) (hac : a < c) (s₀ : Icc a c)
    (hclock : T - s₀.val ^ 2 = t₀.val)
    (htime : ∀ s ∈ Icc a c, T - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ∃ l r : ℝ, a ≤ l ∧ l < r ∧ r ≤ c ∧ s₀.val ∈ Icc l r ∧
      Icc l r ∈ 𝓝[Icc a c] s₀.val ∧
      ∃ x y : G.Point, ∃ p : M14BackwardPath G T (l ^ 2) (r ^ 2) x y,
        ∃ R : M14SquareRootPath G p,
        ∃ E : M14PullbackExtension G R.curve (M14SqrtParameterInterval (l ^ 2) (r ^ 2))
            R.horizontal_velocity,
          (∀ s ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2), ∀ Z,
            M14SquareRootEulerResidual G R E s Z = 0) ∧
          R.curve s₀.val = (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀) ∧
          HEq (R.horizontal_velocity s₀.val) V := by
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀
  let z₀ := (x₀.val, M08.chartMetricOperator W.flow T x₀ (s₀.val, x₀.val) (j.symm V))
  have hx₀ : x₀.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ x₀ = x₀.val := by rw [extChartAt_coe]; rfl
    rw [← hval]
    exact mem_extChartAt_target x₀
  obtain ⟨l, r, s₁, hlr, hal, hrc, hi, hnear, ρ, hρ, α, hα, hdata⟩ :=
    exists_closedChartEulerPhase_joint_family W.flow hM04 T x₀ hac htime s₀
      (z₀ := z₀) hx₀
  have hl : 0 ≤ l := ha.trans hal
  have hr : 0 ≤ r := hl.trans hlr.le
  have hs₀ : s₀.val ∈ Icc l r := hi ▸ s₁.property
  have hC : M14SqrtParameterInterval (l ^ 2) (r ^ 2) = Icc l r := by
    rw [M14SqrtParameterInterval, Real.sqrt_sq hl, Real.sqrt_sq hr]
  have hz : z₀ ∈ ball z₀ ρ := mem_ball_self hρ
  have hsm : ContDiffOn ℝ ∞ (fun s => α (z₀, s)) (Icc l r) :=
    hα.comp (contDiffOn_const.prodMk contDiffOn_id) (fun _ hs => ⟨hz, hs⟩)
  have htime' : ∀ s ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2),
      T - s ^ 2 ∈ (G.gaugeCover.interval b).domain := by
    rw [hC]
    exact fun s hs => htime s ((Icc_subset_Icc hal hrc) hs)
  have hphase := fun s hs => ((hdata z₀ hz).2 s hs).2
  obtain ⟨β, _, hβclock, hβcoord, p, R, E, _, hrec, hEuler, hvel⟩ :=
    exists_gaugeEulerPath_of_phase hM04 hM12 b W t₀ x₀ (sq_nonneg l)
      ((sq_lt_sq₀ hl hr).mpr hlr) htime'
      (q := fun s => (α (z₀, s)).1) (P := fun s => (α (z₀, s)).2)
      (by simpa only [hC] using hsm.fst)
      (by rw [hC]; exact fun s hs => ((hdata z₀ hz).2 s hs).1)
      (by simpa only [hC, Prod.eta] using hphase)
  have hsC : s₀.val ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2) := hC ▸ hs₀
  have hinit : α (z₀, s₀.val) = z₀ := hi ▸ (hdata z₀ hz).1
  have hβ₀ : β s₀.val = (t₀, x₀) := by
    apply Prod.ext
    · exact Subtype.ext ((hβclock s₀.val hsC).trans hclock)
    · exact Subtype.ext ((hβcoord s₀.val hsC).trans (congrArg Prod.fst hinit))
  have hvd : derivWithin (fun s => (α (z₀, s)).1) (Icc l r) s₀.val = j.symm V := by
    have hd₀ : HasDerivWithinAt (fun s => (α (z₀, s)).1)
        (Ring.inverse (M08.chartMetricOperator W.flow T x₀ (s₀.val, (α (z₀, s₀.val)).1))
          (α (z₀, s₀.val)).2) (Icc l r) s₀.val := (hphase s₀.val hs₀).fst
    have hd := hd₀.derivWithin (uniqueDiffOn_Icc hlr s₀.val hs₀)
    rw [hinit] at hd
    exact hd.trans (M08.inverse_operator_apply _
      (M08.chartMetricOperator_isUnit_of_target W.flow T x₀ hx₀) _)
  have hV := hvel s₀.val hsC
  rw [hC, hβ₀, hvd, ContinuousLinearEquiv.apply_symm_apply] at hV
  exact ⟨l, r, hal, hlr, hrc, hs₀, hnear, _, _, p, R, E, hEuler,
    (hrec s₀.val hsC).trans (congrArg (G.gaugeCover.cylinder b).toSpacetime hβ₀), hV⟩






theorem exists_squareRootEulerPath_through_velocity
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T s : ℝ} (hT : T ∈ I.domain) (hs : 0 < s) (q : G.Point)
    (hclock : G.spacetime.timeFunction q = T - s ^ 2) (V : G.Horizontal q) :
    ∃ l r : ℝ, 0 < l ∧ l < s ∧ s ≤ r ∧
      Icc l r ∈ 𝓝[{t | 0 ≤ t ∧ T - t ^ 2 ∈ I.domain}] s ∧
      ∃ x y : G.Point, ∃ p : M14BackwardPath G T (l ^ 2) (r ^ 2) x y,
        ∃ R : M14SquareRootPath G p,
        ∃ E : M14PullbackExtension G R.curve (M14SqrtParameterInterval (l ^ 2) (r ^ 2))
            R.horizontal_velocity,
          (∀ t ∈ M14SqrtParameterInterval (l ^ 2) (r ^ 2), ∀ Z,
            M14SquareRootEulerResidual G R E t Z = 0) ∧
          R.curve s = q ∧ HEq (R.horizontal_velocity s) V := by
  obtain ⟨b, ⟨t₀, x₀⟩, rfl⟩ := G.gaugeCover.covers q
  have hCoordinates := hM12.coordinate_gauges X time I G.spacetime G.slices
    G.timeIntervals G.gaugeCover G.leafwise
  obtain ⟨W⟩ := ordinaryGaugeWitness_nonempty b hCoordinates
  have htime : T - s ^ 2 = t₀.val :=
    hclock.symm.trans ((G.gaugeCover.cylinder b).time_eq (t₀, x₀))
  obtain ⟨a, c, ha, has, hsc, hwindow, hnear⟩ :=
    exists_gauge_positive_squareClock_window b t₀ x₀ hT hs htime
  obtain ⟨l, r, hal, _, _, hslr, hlocal, x, y, p, R, E, hEuler, hpoint, hV⟩ :=
    exists_gaugeEulerPath_through_velocity hM04 hM12 b W t₀ x₀ V ha.le
      (has.trans_le hsc) ⟨s, has.le, hsc⟩ htime hwindow
  have hls : l < s := left_lt_of_Icc_mem_nhdsWithin has hsc hlocal
  exact ⟨l, r, ha.trans_le hal, hls, hslr.2, nhdsWithin_le_of_mem hnear hlocal,
    x, y, p, R, E, hEuler, hpoint, hV⟩

end PoincareConjecture.M14
