import PoincareConjecture.Proofs.M14.Sec6_3_NormalizedPhase
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerExistence










set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Metric
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}




theorem exists_localInitialValuePath_neighborhood_in_gauge
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {smax : ℝ} (hsmax : 0 < smax)
    (htime : ∀ s ∈ Icc 0 smax, t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ∃ s : ℝ, 0 < s ∧ s ≤ smax ∧
      ∃ U : Set (G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))),
        IsOpen U ∧ Z ∈ U ∧ ∀ V ∈ U, ∃ y : G.Point,
          Nonempty (M14SquareRootInitialValuePath G t₀.val (s ^ 2)
            ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) y V) := by
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀
  let B := M08.chartMetricOperator W.flow t₀.val x₀ (0, x₀.val)
  let z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun V => (x₀.val, B ((2 : ℝ) • j.symm V))
  have hz : Continuous z := continuous_const.prodMk
    (B.continuous.comp (j.symm.continuous.const_smul (2 : ℝ)))
  have hx₀ : x₀.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ x₀ = x₀.val := by rw [extChartAt_coe]; rfl
    rw [← hval]
    exact mem_extChartAt_target x₀
  obtain ⟨δ, hδ, r, hr, _, α, _, hα⟩ :=
    exists_closedChartEulerPhase_family W.flow hM04 t₀.val x₀ hsmax htime
      (show (0 : ℝ) ∈ Icc 0 smax from ⟨le_rfl, hsmax.le⟩) (z₀ := z Z) hx₀
  have hleft : max (0 : ℝ) (0 - δ) = 0 := max_eq_left (by linarith)
  rw [hleft, zero_add] at hα
  let c : ℝ := min smax δ
  have hc : 0 < c := lt_min hsmax hδ
  have hcmax : c ≤ smax := min_le_left _ _
  have hC : M14SqrtParameterInterval 0 (c ^ 2) = Icc 0 c := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hc.le]
  refine ⟨c, hc, hcmax, z ⁻¹' ball (z Z) r, isOpen_ball.preimage hz,
    mem_ball_self hr, ?_⟩
  intro V hV
  obtain ⟨hi, hmap, hsm, hd⟩ := hα (z V) (ball_subset_closedBall hV)
  refine exists_initialValuePath_of_momentum_phase hM04 hM12 b W t₀ x₀ V
    (sq_pos_of_pos hc) (q := fun s => (α (z V, s)).1) (P := fun s => (α (z V, s)).2)
    ?_ ?_ ?_ ?_ hi
  · intro s hs
    rw [hC] at hs
    exact htime s ⟨hs.1, hs.2.trans hcmax⟩
  · rw [hC]
    exact hsm.fst
  · rw [hC]
    exact hmap
  · rw [hC]
    exact hd




theorem exists_localInitialValuePath_in_gauge
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {smax : ℝ} (hsmax : 0 < smax)
    (htime : ∀ s ∈ Icc 0 smax, t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ∃ s : ℝ, 0 < s ∧ s ≤ smax ∧ ∃ y : G.Point,
      Nonempty (M14SquareRootInitialValuePath G t₀.val (s ^ 2)
        ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) y Z) := by
  obtain ⟨s, hs, hsmax, U, _, hZU, hU⟩ :=
    exists_localInitialValuePath_neighborhood_in_gauge hM04 hM12 b W t₀ x₀ Z hsmax htime
  exact ⟨s, hs, hsmax, hU Z hZU⟩

end PoincareConjecture.M14
