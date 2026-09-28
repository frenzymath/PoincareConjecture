import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerJointFamily
import PoincareConjecture.Proofs.M14.Sec6_3_GaugeFamilyLift
import PoincareConjecture.Proofs.M14.Sec6_3_RealizedInitialPhase
import PoincareConjecture.Proofs.M14.Sec6_3_MaximalCoherence

set_option autoImplicit false

open Set Metric
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

private theorem horizontal_t2Space {x : G.Point} : T2Space (G.Horizontal x) :=
  FiberBundle.t2Space (EuclideanSpace ℝ (Fin n)) G.Horizontal x

attribute [local instance] horizontal_t2Space

set_option maxHeartbeats 800000 in

theorem initialValueCurve_smooth_initial_tube_in_gauge
    (hM04 : RicciFlowCurvatureTheory.{0}) (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (b : G.gaugeCover.index)
    (W : OrdinaryGaugeWitness G.leafwise (G.gaugeCover.cylinder b) (G.gaugeCover.metric b))
    (t₀ : (G.timeIntervals.interval (G.gaugeCover.interval b)).Point)
    (x₀ : G.gaugeCover.spatial b)
    (Z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
    {smax : ℝ} (hsmax : 0 < smax)
    (htime : ∀ s ∈ Icc 0 smax, t₀.val - s ^ 2 ∈ (G.gaugeCover.interval b).domain) :
    ∃ d : ℝ, 0 < d ∧ d ≤ smax ∧
      ∃ U : Set (G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))),
        IsOpen U ∧ Z ∈ U ∧
        U ×ˢ Icc 0 d ⊆ initialValueDomain G t₀.val
          ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) ∧
        M14HorizontalFamilySmooth G
          (initialValueCurve G t₀.val ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))
          (U ×ˢ Icc 0 d) := by
  let base := (G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)
  let metric := G.spacetime.horizontalMetric.toRiemannianMetric
  let : NormedAddCommGroup (G.Horizontal base) :=
    (metric.toCore base).toNormedAddCommGroupOfTopology
      (metric.continuousAt base) (metric.isVonNBounded base)
  let : InnerProductSpace ℝ (G.Horizontal base) :=
    .ofCoreOfTopology (metric.toCore base) (metric.continuousAt base) (metric.isVonNBounded base)
  let : Bundle.RiemannianBundle (G.Horizontal : G.Point → Type _) :=
    ⟨metric⟩
  let j := (G.gaugeCover.metric b).spatialTangentEquiv t₀ x₀
  let L : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) →L[ℝ]
      EuclideanSpace ℝ (Fin n) := j.symm.toContinuousLinearMap
  let B := M08.chartMetricOperator W.flow t₀.val x₀ (0, x₀.val)
  let z : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) →
      EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) :=
    fun V => (x₀.val, B ((2 : ℝ) • j.symm V))
  have hz : ContDiff ℝ ∞ z := contDiff_const.prodMk
    (B.contDiff.comp (L.contDiff.const_smul (2 : ℝ)))
  have hx₀ : x₀.val ∈ (extChartAt (𝓡 n) x₀).target := by
    have hval : extChartAt (𝓡 n) x₀ x₀ = x₀.val := by rw [extChartAt_coe]; rfl
    rw [← hval]
    exact mem_extChartAt_target x₀
  obtain ⟨c, d, s₁, hcd, h0c, hdsmax, hi, _, ρ, hρ, α, hα, hdata⟩ :=
    exists_closedChartEulerPhase_joint_family W.flow hM04 t₀.val x₀ hsmax htime
      ⟨0, le_rfl, hsmax.le⟩ (z₀ := z Z) hx₀
  have hs₁ : s₁.val = 0 := hi
  have hc : c = 0 := le_antisymm (by simpa only [hs₁] using s₁.property.1) h0c
  subst c
  let U := z ⁻¹' ball (z Z) ρ
  have hU : IsOpen U := isOpen_ball.preimage hz.continuous
  have hZU : Z ∈ U := mem_ball_self hρ
  have hphase : ContDiffOn ℝ ∞ (fun w => α (z w.1, w.2)) (U ×ˢ Icc 0 d) :=
    hα.comp ((hz.contDiffOn.comp contDiffOn_fst (fun _ _ => mem_univ _)).prodMk
      contDiffOn_snd) (fun _ hw => hw)
  have hC : M14SqrtParameterInterval 0 (d ^ 2) = Icc 0 d := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hcd.le]
  have hclock : ∀ w ∈ U ×ˢ Icc 0 d,
      t₀.val - w.2 ^ 2 ∈ (G.gaugeCover.interval b).domain :=
    fun w hw => htime w.2 ⟨hw.2.1, hw.2.2.trans hdsmax⟩
  obtain ⟨β, hβ, hβclock, hβcoord⟩ := exists_smooth_gaugeLift_of_maps
    ((𝓘(ℝ, G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)))).prod (𝓘(ℝ, ℝ)))
    b t₀ x₀ ((contMDiffOn_const.sub (contMDiffOn_snd.pow 2))) hclock
    (by
      rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
      exact hphase.fst.contMDiffOn)
    (fun w hw => ((hdata (z w.1) hw.1).2 w.2 hw.2).1)
  have hpaths (V : G.Horizontal ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀))) (hV : V ∈ U) :
      ∃ y : G.Point, ∃ Q : M14SquareRootInitialValuePath G t₀.val (d ^ 2)
          ((G.gaugeCover.cylinder b).toSpacetime (t₀, x₀)) y V,
        EqOn Q.square_path.curve (fun s => (G.gaugeCover.cylinder b).toSpacetime (β (V, s)))
          (Icc 0 d) := by
    have hq := hphase.fst.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun s hs => ⟨hV, hs⟩)
    have hp : ∀ s ∈ Icc 0 d, HasDerivWithinAt (fun r => α (z V, r))
        (M08.closedChartEulerPhase W.flow t₀.val x₀ (Icc 0 d) s (α (z V, s)))
        (Icc 0 d) s := fun s hs => ((hdata (z V) hV).2 s hs).2
    have hini : α (z V, 0) = z V := by simpa only [hs₁] using (hdata (z V) hV).1
    have h := exists_initialValuePath_realizing_momentum_phase hM04 hM12 b W t₀ x₀ V
      (sq_pos_of_pos hcd) (q := fun s => (α (z V, s)).1) (P := fun s => (α (z V, s)).2)
      (by simpa only [hC] using fun s hs => hclock (V, s) ⟨hV, hs⟩)
      (by simpa only [hC, Function.comp_def, id_eq] using hq)
      (by rw [hC]; exact fun s hs => ((hdata (z V) hV).2 s hs).1)
      (by simpa only [hC, Prod.eta] using hp) hini (fun s => β (V, s))
      (by simpa only [hC] using fun s hs => hβclock (V, s) ⟨hV, hs⟩)
      (by simpa only [hC] using fun s hs => hβcoord (V, s) ⟨hV, hs⟩)
    simpa only [hC] using h
  refine ⟨d, hcd, hdsmax, U, hU, hZU, ?_, ?_⟩
  · intro w hw
    obtain ⟨y, Q, _⟩ := hpaths w.1 hw.1
    exact initialValueDomain_prefix (Or.inr ⟨hcd, y, ⟨Q⟩⟩) hw.2.1 hw.2.2
  · have hsm := (G.gaugeCover.cylinder b).smooth.comp_contMDiffOn hβ
    apply hsm.congr
    intro w hw
    obtain ⟨_, Q, hQ⟩ := hpaths w.1 hw.1
    have heq := initialValueCurve_eqOn_square hM04 hM12 Q
    rw [hC] at heq
    exact (heq hw.2).trans (hQ hw.2)

end PoincareConjecture.M14
