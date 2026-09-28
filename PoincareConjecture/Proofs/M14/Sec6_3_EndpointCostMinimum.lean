import PoincareConjecture.Proofs.M14.Sec6_3_EndpointCost
import PoincareConjecture.Proofs.M14.Sec6_3_SquareCornerComparison

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology intervalIntegral

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}
  {f : ℝ × ℝ → G.Point} {U : Set ℝ} {T b c : ℝ}
  {j : G.gaugeCover.index}
  {lift : G.Point → (G.timeIntervals.interval (G.gaugeCover.interval j)).Point ×
    G.gaugeCover.spatial j} {x y : G.Point}

namespace GaugeEndpointFamily

variable (D : GaugeEndpointFamily f U T 0 b c 0 j lift)

theorem cost_zero_eq_action (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) (m : M14BackwardPath G T 0 (b ^ 2) x y)
    (heq : EqOn (fun t => f (Real.sqrt t, 0)) m.curve (Icc 0 (b ^ 2))) :
    D.cost (0, 0) = M14BackwardLAction G m := by
  have hb : 0 < b := hc.1.trans hc.2
  have hC : M14SqrtParameterInterval 0 (b ^ 2) = Icc 0 b := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hb.le]
  let α := fun s => D.family (s, (0, (lift (f (c, 0))).2.val))
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (Icc 0 b) :=
    D.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn
      (fun _ hs => ⟨hs, D.center_mem⟩)
  have hclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 (b ^ 2)) :
      G.spacetime.timeFunction (α s) = T - s ^ 2 := D.clock s (hC ▸ hs) _ D.center_mem
  have hcurve : EqOn (fun t => α (Real.sqrt t)) m.curve (Icc 0 (b ^ 2)) := by
    intro t ht
    have hs : Real.sqrt t ∈ Icc 0 b :=
      ⟨Real.sqrt_nonneg t, (Real.sqrt_le_sqrt ht.2).trans_eq (Real.sqrt_sq hb.le)⟩
    exact (D.recovery _ D.center_mem _ hs).trans (heq ht)
  have htotal : (∫ s in 0..b, squareCurveDensity G α (Icc 0 b) s) = M14BackwardLAction G m := by
    simpa only [hC, Real.sqrt_zero, Real.sqrt_sq hb.le] using
      integral_squareCurveDensity_eq_action_of_curve hM12 m α (hC.symm ▸ hα) hclock hcurve
  have hd := (squareCurveDensity_contDiffOn hM12 (uniqueDiffOn_Icc hb) hα).continuousOn
  have hpre : IntervalIntegrable (squareCurveDensity G α (Icc 0 b)) MeasureTheory.volume 0 c :=
    (hd.mono (fun _ hs => ⟨hs.1, hs.2.trans hc.2.le⟩)).intervalIntegrable_of_Icc hc.1.le
  have htail : IntervalIntegrable (squareCurveDensity G α (Icc 0 b)) MeasureTheory.volume c b :=
    (hd.mono (fun _ hs => ⟨hc.1.le.trans hs.1, hs.2⟩)).intervalIntegrable_of_Icc hc.2.le
  simpa only [cost, prefixAction, tailAction, squareFamilyAction, add_zero, α] using
    (intervalIntegral.integral_add_adjacent_intervals hpre htail).trans htotal

theorem cost_isLocalMin (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    (hc : c ∈ Ioo 0 b) (m : M14BackwardPath G T 0 (b ^ 2) x y)
    (hmin : M14IsMinimizing m)
    (heq : EqOn (fun t => f (Real.sqrt t, 0)) m.curve (Icc 0 (b ^ 2)))
    (hleft : ∀ r ∈ U, f (0, r) = x) (hright : f (b, 0) = y) :
    IsLocalMin D.cost (0, 0) := by
  have hb : 0 < b := hc.1.trans hc.2
  have hC : M14SqrtParameterInterval 0 (b ^ 2) = Icc 0 b := by
    rw [M14SqrtParameterInterval, Real.sqrt_zero, Real.sqrt_sq hb.le]
  let A := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    (z.1, (lift (f (c, z.1))).2.val + z.2)
  let B := fun z : ℝ × EuclideanSpace ℝ (Fin n) =>
    ((0 : ℝ), (lift (f (c, z.1))).2.val + z.2)
  have ha : ContinuousAt
      (fun z : ℝ × EuclideanSpace ℝ (Fin n) => (lift (f (c, z.1))).2.val + z.2) (0, 0) :=
    (D.coordinate_smooth.comp (0, 0) contDiffAt_fst).continuousAt.add continuousAt_snd
  have hAN : D.parameters ∈ 𝓝 (A (0, 0)) := by
    simpa only [A, add_zero] using D.parameters_open.mem_nhds D.center_mem
  have hBN : D.parameters ∈ 𝓝 (B (0, 0)) := by
    simpa only [B, add_zero] using D.parameters_open.mem_nhds D.center_mem
  have hA := (continuousAt_fst.prodMk ha).preimage_mem_nhds hAN
  have hB := (continuousAt_const.prodMk ha).preimage_mem_nhds hBN
  change ∀ᶠ z in 𝓝 (0, 0), D.cost (0, 0) ≤ D.cost z
  rw [D.cost_zero_eq_action hM12 hc m heq]
  filter_upwards [hA, hB] with z hzA hzB
  let α := fun s => D.family (s, A z)
  let β := fun s => D.family (s, B z)
  have hα : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ α (Icc 0 b) :=
    D.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs => ⟨hs, hzA⟩)
  have hβ : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ β (Icc 0 b) :=
    D.smooth.comp (contMDiff_id.prodMk contMDiff_const).contMDiffOn (fun _ hs => ⟨hs, hzB⟩)
  have hαclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 (b ^ 2)) :
      G.spacetime.timeFunction (α s) = T - s ^ 2 := D.clock s (hC ▸ hs) _ hzA
  have hβclock (s : ℝ) (hs : s ∈ M14SqrtParameterInterval 0 (b ^ 2)) :
      G.spacetime.timeFunction (β s) = T - s ^ 2 := D.clock s (hC ▸ hs) _ hzB
  have hαx : α (Real.sqrt 0) = x := by
    rw [Real.sqrt_zero]
    exact (D.initial _ hzA).trans (hleft _ (D.parameter_subset _ hzA))
  have hβx : β (Real.sqrt 0) = x := by
    rw [Real.sqrt_zero]
    exact (D.initial _ hzB).trans (hleft _ (D.parameter_subset _ hzB))
  have hβy : β (Real.sqrt (b ^ 2)) = y := by
    rw [Real.sqrt_sq hb.le]
    exact (D.final _ hzB).trans hright
  have hjoin : α (Real.sqrt (c ^ 2)) = β (Real.sqrt (c ^ 2)) := by
    rw [Real.sqrt_sq hc.1.le]
    obtain ⟨hyA, hmA⟩ := D.marked _ hzA
    obtain ⟨hyB, hmB⟩ := D.marked _ hzB
    exact hmA.trans hmB.symm
  have hcc : c ^ 2 ∈ Ioo 0 (b ^ 2) := ⟨sq_pos_of_pos hc.1, sq_lt_sq' (by linarith [hc.1]) hc.2⟩
  have hcomp := minimizing_action_le_square_prefix_add_tail hM12 m hmin hcc α β
    (hC.symm ▸ hα) (hC.symm ▸ hβ) hαclock hβclock hαx hβx hβy hjoin
  simpa only [cost, prefixAction, tailAction, squareFamilyAction, M14SqrtParameterInterval,
    Real.sqrt_zero, Real.sqrt_sq hb.le, Real.sqrt_sq hc.1.le, α, β, A, B] using hcomp

end GaugeEndpointFamily

end PoincareConjecture.M14
