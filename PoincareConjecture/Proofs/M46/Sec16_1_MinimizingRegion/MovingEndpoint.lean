import PoincareConjecture.Proofs.M46.Sec16_1_MinimizingRegion.DisplacementAction
import PoincareConjecture.Proofs.M14.Sec6_2_GaugeLift

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.Proofs.M46

variable {n : ℕ} {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport n X time I}

theorem moving_endpoint_recovery
    (hM12 : GeneralizedRicciGaugeTheory.{u} n)
    {T tau b B : ℝ} {x y : G.Point}
    (p : M14BackwardPath G T 0 tau x y) (hp : M14BackwardLAction G p < B)
    (gamma : ℝ → G.Point) (hs : Real.sqrt tau ≤ b)
    (hgamma : ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel n) ∞ gamma (Icc 0 b))
    (hclock : ∀ s ∈ Icc 0 b, G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (hx : gamma 0 = x)
    (htrace : EqOn p.curve (fun t => gamma (Real.sqrt t)) (Icc 0 tau)) :
    ∃ V : Set G.Point, IsOpen V ∧ y ∈ V ∧
      ∀ z ∈ V, 0 < T - G.spacetime.timeFunction z →
        Real.sqrt (T - G.spacetime.timeFunction z) ≤ b →
        ∃ q : M14BackwardPath G T 0 (T - G.spacetime.timeFunction z) x z,
          M14BackwardLAction G q < B := by
  let sqtime := fun z : G.Point => Real.sqrt (T - G.spacetime.timeFunction z)
  have hsy : sqtime y = Real.sqrt tau := by
    dsimp only [sqtime]
    rw [p.endpoint_time]
    congr 1
    ring
  have hc : Real.sqrt tau ∈ Ioc 0 b := ⟨Real.sqrt_pos.mpr p.tau_lt, hs⟩
  have hb : 0 < b := hc.1.trans_le hc.2
  have hgy : gamma (sqtime y) = y := by
    rw [hsy]
    exact (htrace ⟨p.tau_lt.le, le_rfl⟩).symm.trans p.curve_end
  obtain ⟨j, U, lift, hU, hyU, hlift, hright, hliftClock⟩ := M14.exists_smooth_gauge_lift G y
  obtain ⟨D⟩ := endpointDisplacementFamily_nonempty gamma hc hgamma hclock
    j lift hU hlift hright hliftClock (by rw [← hsy, hgy]; exact hyU)
  let K : Set G.Point := {z | sqtime z ∈ Icc 0 b}
  have hyK : y ∈ K := by
    change sqtime y ∈ Icc 0 b
    rw [hsy]
    exact ⟨hc.1.le, hc.2⟩
  have htime : Continuous G.spacetime.timeFunction :=
    (show ContMDiff (spacetimeModel n) (𝓘(ℝ, ℝ)) ∞ G.spacetime.timeFunction from
      G.spacetime.time_smooth).continuous
  have hsqtime : Continuous sqtime := Real.continuous_sqrt.comp (continuous_const.sub htime)
  have hg : ContinuousWithinAt (fun z => gamma (sqtime z)) K y :=
    (hgamma _ hyK).continuousWithinAt.comp hsqtime.continuousAt.continuousWithinAt
      (fun _ hz => hz)
  have hgU : gamma (sqtime y) ∈ U := hgy.symm ▸ hyU
  have hL : ContinuousAt lift y := (hlift y hyU).continuousWithinAt.continuousAt (hU.mem_nhds hyU)
  have hLg : ContinuousWithinAt (fun z => lift (gamma (sqtime z))) K y :=
    ((hlift _ hgU).continuousWithinAt.continuousAt (hU.mem_nhds hgU)).comp_continuousWithinAt
      (f := fun z : G.Point => gamma (sqtime z)) hg
  have hchi : Continuous (fun z : G.Point => D.cutoff (sqtime z)) :=
    D.cutoff_smooth.continuous.comp hsqtime
  have hchiY : D.cutoff (sqtime y) ≠ 0 := by
    rw [hsy, D.cutoff_center]
    exact one_ne_zero
  let par := fun z : G.Point => (D.cutoff (sqtime z))⁻¹ •
    ((lift z).2.val - (lift (gamma (sqtime z))).2.val)
  have hpar : ContinuousWithinAt par K y :=
    (hchi.continuousAt.inv₀ hchiY).continuousWithinAt.smul
      ((continuous_subtype_val.continuousAt.comp hL.snd).continuousWithinAt.sub
        (continuous_subtype_val.continuousAt.comp_continuousWithinAt hLg.snd))
  have hparY : par y = 0 := by simp only [par, hgy, sub_self, smul_zero]
  have hparN : ∀ᶠ z in 𝓝[K] y, par z ∈ D.parameters :=
    hpar.preimage_mem_nhdsWithin (D.parameters_open.mem_nhds (hparY.symm ▸ D.zero_mem))
  have hpair : Tendsto (fun z => (par z, sqtime z)) (𝓝[K] y)
      (𝓝[D.parameters ×ˢ Icc 0 b] (0, Real.sqrt tau)) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · simpa only [hparY, hsy] using hpar.tendsto.prodMk_nhds
        hsqtime.continuousAt.continuousWithinAt.tendsto
    · filter_upwards [hparN, self_mem_nhdsWithin] with z hzN hzK
      exact ⟨hzN, hzK⟩
  have hcost : Tendsto (fun z => D.cost (par z, sqtime z)) (𝓝[K] y)
      (𝓝 (M14BackwardLAction G p)) := by
    have hc0 := ((D.cost_contDiffOn hM12 hb).continuousOn
      (0, Real.sqrt tau) ⟨D.zero_mem, hc.1.le, hc.2⟩).tendsto
    rw [D.cost_zero hM12 p hs hx htrace] at hc0
    exact hc0.comp hpair
  have hgood : {z : G.Point | z ∈ U ∧ gamma (sqtime z) ∈ U ∧
      D.cutoff (sqtime z) ≠ 0 ∧ par z ∈ D.parameters ∧ D.cost (par z, sqtime z) < B}
      ∈ 𝓝[K] y := by
    filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hyU),
      hg.preimage_mem_nhdsWithin (hU.mem_nhds hgU),
      mem_nhdsWithin_of_mem_nhds (hchi.continuousAt.eventually_ne hchiY),
      hparN, hcost.eventually (Iio_mem_nhds hp)] with z hz hgZ hne hN hB
    exact ⟨hz, hgZ, hne, hN, hB⟩
  obtain ⟨V, hV, hyV, hVK⟩ := mem_nhdsWithin.mp hgood
  refine ⟨V, hV, hyV, ?_⟩
  intro z hz ht hztime
  have hzK : z ∈ K := ⟨Real.sqrt_nonneg _, hztime⟩
  obtain ⟨hzU, hgzU, hchiz, hzN, hzB⟩ := hVK ⟨hz, hzK⟩
  have hend : D.family (sqtime z, par z) = z :=
    D.target (sqtime z) hzK hgzU hchiz z hzU (by
      dsimp only [sqtime]
      rw [Real.sq_sqrt ht.le]
      ring)
  obtain ⟨q, _, hq⟩ := D.exists_path hM12 ht hztime hzN hx hend
  exact ⟨q, hq.trans_lt hzB⟩

end PoincareConjecture.Proofs.M46
