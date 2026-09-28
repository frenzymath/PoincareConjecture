import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Bounds
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Soliton.ThreeDimensional.Asymptotic.Positivity
import PoincareConjecture.Proofs.Horizon.Analysis.Parabolic.PointPicking
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace Poincare.AncientVolume

theorem exists_curvature_controlled_point_of_continuous
    {X : Type*} [MetricSpace X] [ProperSpace X]
    (R : X → ℝ) (hR : ∀ y, 0 ≤ R y) (hcontinuous : Continuous R)
    (p x : X) (hd : 0 < dist p x) (hx : 0 < R x) :
    ∃ q : X, ∃ r : ℝ, q ∈ Metric.ball x (dist p x / 2) ∧
      0 < r ∧ R x ≤ R q ∧ dist p x / 2 ≤ dist p q ∧
      r * Real.sqrt (R q) = dist p x * Real.sqrt (R x) / 4 ∧
      Metric.ball q r ⊆ Metric.ball x (dist p x / 2) ∧
      ∀ y ∈ Metric.ball q r, R y ≤ 4 * R q := by
  let f : X → ℝ := fun y => Real.sqrt (R y)
  let S := Metric.closedBall x (dist p x / 2)
  let L : ℝ := dist p x * f x / 4
  have hfx : 0 < f x := Real.sqrt_pos.mpr hx
  have hL : 0 < L := by dsimp [L]; positivity
  have hbound : BddAbove (f '' S) :=
    (isCompact_closedBall x (dist p x / 2)).bddAbove_image
      (Real.continuous_sqrt.comp hcontinuous).continuousOn
  obtain ⟨q, _, _, hscore, hmargin, hcontrol⟩ :=
    Poincare.Parabolic.exists_point_with_doubling_bound S f (dist x)
      (fun _ => 0) hbound hL.le (Metric.mem_closedBall_self (by positivity)) hfx
  have hfq : 0 < f q := hfx.trans_le hscore
  let r : ℝ := L / f q
  have hr : 0 < r := div_pos hL hfq
  have hbudget : dist x q + 2 * r ≤ dist p x / 2 := by
    have hcancel : 2 * L / f x = dist p x / 2 := by
      dsimp [L]
      field_simp
      ring
    simpa only [dist_self, zero_add, hcancel, mul_div_assoc] using hmargin
  have hq : q ∈ Metric.ball x (dist p x / 2) := by
    rw [Metric.mem_ball, dist_comm]
    linarith
  have hsubset : Metric.ball q r ⊆ Metric.ball x (dist p x / 2) := by
    intro y hy
    have hqy : dist q y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have htri := dist_triangle x q y
    rw [Metric.mem_ball, dist_comm]
    linarith
  refine ⟨q, r, hq, hr, ?_, ?_, ?_, hsubset, ?_⟩
  · exact (Real.sqrt_le_sqrt_iff (hR q)).mp hscore
  · have htri := dist_triangle p q x
    have hqx := Metric.mem_ball.mp hq
    linarith
  · dsimp [r, L]
    rw [div_mul_cancel₀ _ hfq.ne']
  · intro y hy
    have hqy : dist q y < r := by simpa [dist_comm] using Metric.mem_ball.mp hy
    have hyS : y ∈ S := Metric.ball_subset_closedBall (hsubset hy)
    have hfy : f y ≤ 2 * f q := hcontrol y hyS le_rfl (by
      have htri := dist_triangle x q y
      dsimp [r] at hqy
      linarith)
    have hsq := mul_self_le_mul_self (Real.sqrt_nonneg (R y)) hfy
    dsimp [f] at hsq
    nlinarith [Real.sq_sqrt (hR y), Real.sq_sqrt (hR q)]

end Poincare.AncientVolume

namespace PoincareConjecture.AncientAsymptoticSolitonLimitData

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {S : AncientRescalingSequence K}

theorem exists_backward_curvature_controlled_point
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    {t : ℝ} (ht : t < 0) (p x : L.convergence.limit.carrier.carrier)
    (hd : 0 < ((L.convergence.limit.flow.metric t).edist p x).toReal) :
    let g := L.convergence.limit.flow.metric t
    let R := (L.convergence.limit.flow.connection t).scalarCurvature
    ∃ q : L.convergence.limit.carrier.carrier, ∃ r : ℝ,
      q ∈ g.ball x ((g.edist p x).toReal / 2) ∧
      0 < r ∧ R x ≤ R q ∧ (g.edist p x).toReal / 2 ≤ (g.edist p q).toReal ∧
      r * Real.sqrt (R q) = (g.edist p x).toReal * Real.sqrt (R x) / 4 ∧
      g.ball q r ⊆ g.ball x ((g.edist p x).toReal / 2) ∧
      (∀ y ∈ g.ball q r, R y ≤ 4 * R q) ∧
      ∀ s ≤ t, ∀ y ∈ g.ball q r,
        (L.convergence.limit.flow.connection s).curvatureTensorNorm y ≤ 36 * R q := by
  let C := L.convergence.limit.carrier
  let g := L.convergence.limit.flow.metric t
  let R := (L.convergence.limit.flow.connection t).scalarCurvature
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : C.carrier → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ ↦ rfl⟩⟩
  let : EMetricSpace C.carrier := EMetricSpace.ofRiemannianMetric (𝓡 3) C.carrier
  let : MetricSpace C.carrier := EMetricSpace.toMetricSpace (g.edist_ne_top)
  let : ProperSpace C.carrier := g.properSpace_toMetricSpace (L.convergence.limit.complete t ht)
  have hdist (a b : C.carrier) : dist a b = (g.edist a b).toReal := rfl
  have hball (z : C.carrier) (s : ℝ) : Metric.ball z s = g.ball z s := by
    ext y
    change dist y z < s ↔ g.edist z y < ENNReal.ofReal s
    rw [dist_comm]
    exact edist_lt_ofReal.symm
  obtain ⟨q, r, hq, hr, hR, hdistq, hscale, hsubset, hcontrol⟩ :=
    Poincare.AncientVolume.exists_curvature_controlled_point_of_continuous R
      (fun y => (L.scalarCurvature_pos hC t ht y).le)
      (L.convergence.limit.continuous_scalarCurvature hC t) p x hd
      (L.scalarCurvature_pos hC t ht x)
  simp only [hdist, hball] at hq hdistq hscale hsubset hcontrol
  refine ⟨q, r, hq, hr, hR, hdistq, hscale, hsubset, hcontrol, ?_⟩
  intro s hs y hy
  have hs0 : s < 0 := hs.trans_lt ht
  have hmono := L.convergence.limit.scalarCurvature_monotoneOn_of_derivative_nonnegative
    L.scalar_curvature_nonnegative_time_derivative y hs0 ht hs
  have hnorm := L.convergence.limit.curvatureTensorNorm_le_scalarCurvature hC s hs0 y
  have hselected := hcontrol y hy
  dsimp [R] at hselected ⊢
  linarith

theorem exists_escaping_backward_controlled_sequence_of_unbounded_curvature
    (hC : RicciFlowCurvatureTheory.{u}) (L : AncientAsymptoticSolitonLimitData S)
    {t : ℝ} (ht : t < 0) (p : L.convergence.limit.carrier.carrier)
    (hunbounded : ¬ BddAbove
      (range (L.convergence.limit.flow.connection t).scalarCurvature)) :
    let g := L.convergence.limit.flow.metric t
    let R := (L.convergence.limit.flow.connection t).scalarCurvature
    ∃ (q : ℕ → L.convergence.limit.carrier.carrier) (r : ℕ → ℝ),
      (∀ i, 0 < R (q i) ∧ 0 < r i ∧
        (∀ y ∈ g.ball (q i) (r i), R y ≤ 4 * R (q i)) ∧
        ∀ s ≤ t, ∀ y ∈ g.ball (q i) (r i),
          (L.convergence.limit.flow.connection s).curvatureTensorNorm y ≤ 36 * R (q i)) ∧
      Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop ∧
      Tendsto (fun i => R (q i)) atTop atTop ∧
      Tendsto (fun i => r i * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => (g.edist p (q i)).toReal * Real.sqrt (R (q i))) atTop atTop ∧
      Tendsto (fun i => r i / (g.edist p (q i)).toReal) atTop (𝓝 0) := by
  classical
  let C := L.convergence.limit.carrier
  let g := L.convergence.limit.flow.metric t
  let R := (L.convergence.limit.flow.connection t).scalarCurvature
  let : ConnectedSpace C.carrier := connectedSpace_iff_univ.mpr C.connected
  let := g.toMetricSpace
  let : ProperSpace C.carrier := g.properSpace_toMetricSpace (L.convergence.limit.complete t ht)
  have hdist (a b : C.carrier) : dist a b = (g.edist a b).toReal := rfl
  have hchoose (i : ℕ) : ∃ q : C.carrier, ∃ r : ℝ,
      0 < R q ∧ 0 < r ∧
      (∀ y ∈ g.ball q r, R y ≤ 4 * R q) ∧
      (∀ s ≤ t, ∀ y ∈ g.ball q r,
        (L.convergence.limit.flow.connection s).curvatureTensorNorm y ≤ 36 * R q) ∧
      (i : ℝ) ≤ (g.edist p q).toReal ∧ (i : ℝ) ≤ R q ∧
      (i : ℝ) ≤ r * Real.sqrt (R q) ∧
      (i : ℝ) ≤ (g.edist p q).toReal * Real.sqrt (R q) ∧
      r / (g.edist p q).toReal ≤ 1 / ((i : ℝ) + 1) := by
    obtain ⟨B, hB⟩ := (isCompact_closedBall p (2 * ((i : ℝ) + 1) ^ 2)).bddAbove_image
      (L.convergence.limit.continuous_scalarCurvature hC t).continuousOn
    obtain ⟨v, ⟨x, rfl⟩, hx⟩ := not_bddAbove_iff.mp hunbounded (max B (max (i : ℝ) 16))
    have hxB : B < R x := lt_of_le_of_lt (le_max_left _ _) hx
    have hxi : (i : ℝ) < R x :=
      lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hx
    have hx16 : 16 < R x :=
      lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hx
    have hxoutside : x ∉ Metric.closedBall p (2 * ((i : ℝ) + 1) ^ 2) := by
      intro hxmem
      exact (not_le_of_gt hxB) (hB (mem_image_of_mem _ hxmem))
    have hdlarge : 2 * ((i : ℝ) + 1) ^ 2 < (g.edist p x).toReal := by
      simpa only [Metric.mem_closedBall, dist_comm x p, hdist, not_le] using hxoutside
    have hd : 0 < (g.edist p x).toReal := by
      nlinarith [sq_nonneg ((i : ℝ) + 1)]
    obtain ⟨q, r, _, hr, hRxq, hdistq, hscale, _, hcontrol, hpast⟩ :=
      L.exists_backward_curvature_controlled_point hC ht p x hd
    have hqx : 0 < R q := (by linarith : 0 < R x).trans_le hRxq
    have hrootx : 4 < Real.sqrt (R x) := by
      have hs := Real.sq_sqrt (show 0 ≤ R x by linarith)
      nlinarith [Real.sqrt_nonneg (R x)]
    have hrootq : 1 ≤ Real.sqrt (R q) := by
      have hs := Real.sqrt_le_sqrt hRxq
      linarith
    have hi : 0 < (i : ℝ) + 1 := by positivity
    have hi1 : 1 ≤ (i : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) i]
    have hqdist : (i : ℝ) ≤ (g.edist p q).toReal := by nlinarith
    have hdqpos : 0 < (g.edist p q).toReal := by linarith
    have hrupper : r ≤ (g.edist p q).toReal := by
      have hsxq := Real.sqrt_le_sqrt hRxq
      have hmul := mul_le_mul_of_nonneg_left hsxq hd.le
      have hsqpos : 0 < Real.sqrt (R q) := Real.sqrt_pos.mpr hqx
      nlinarith [hscale]
    let a := r / ((i : ℝ) + 1)
    have ha : 0 < a := div_pos hr hi
    have har : a ≤ r := div_le_self hr.le hi1
    refine ⟨q, a, hqx, ha, ?_, ?_, hqdist, hxi.le.trans hRxq, ?_, ?_, ?_⟩
    · intro y hy
      exact hcontrol y (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal har))
    · intro s hs y hy
      exact hpast s hs y (lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal har))
    · have hmul := mul_le_mul_of_nonneg_left hrootx.le hd.le
      have hscaleLarge : ((i : ℝ) + 1) ^ 2 ≤ r * Real.sqrt (R q) := by
        linarith
      have hdiv := div_le_div_of_nonneg_right hscaleLarge hi.le
      have hcancel : ((i : ℝ) + 1) ^ 2 / ((i : ℝ) + 1) = (i : ℝ) + 1 := by
        field_simp
      rw [hcancel] at hdiv
      calc
        (i : ℝ) ≤ (i : ℝ) + 1 := by linarith
        _ ≤ r * Real.sqrt (R q) / ((i : ℝ) + 1) := hdiv
        _ = a * Real.sqrt (R q) := by dsimp [a]; ring
    · exact hqdist.trans (le_mul_of_one_le_right ENNReal.toReal_nonneg hrootq)
    · apply (div_le_iff₀ hdqpos).mpr
      calc
        a ≤ (g.edist p q).toReal / ((i : ℝ) + 1) :=
          div_le_div_of_nonneg_right hrupper hi.le
        _ = (1 / ((i : ℝ) + 1)) * (g.edist p q).toReal := by ring
  choose q r hpos hr hcontrol hpast hdistq hscalar hscale hscaledDist hratio using hchoose
  refine ⟨q, r, fun i => ⟨hpos i, hr i, hcontrol i, hpast i⟩, ?_, ?_, ?_, ?_, ?_⟩
  · exact tendsto_atTop_mono hdistq tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscalar tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscale tendsto_natCast_atTop_atTop
  · exact tendsto_atTop_mono hscaledDist tendsto_natCast_atTop_atTop
  · apply squeeze_zero (fun i => div_nonneg (hr i).le ENNReal.toReal_nonneg) hratio
    exact tendsto_const_nhds.div_atTop (tendsto_atTop_mono
      (fun i => show (i : ℝ) ≤ (i : ℝ) + 1 by linarith) tendsto_natCast_atTop_atTop)

end PoincareConjecture.AncientAsymptoticSolitonLimitData
