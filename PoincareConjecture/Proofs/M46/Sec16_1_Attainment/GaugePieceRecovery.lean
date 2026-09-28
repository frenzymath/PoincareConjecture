import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoverySequence










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}




theorem gauge_piece_recovery_sequence (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (u : ∀ i, ℝ → G.gaugeCover.spatial (R.gauge i).index)
    (hu : ∀ i, ContinuousOn (u i) (Icc (R.node i.castSucc) (R.node i.succ)))
    (hleft : ∀ i, u i (R.node i.castSucc) = ((R.gauge i).lift (gamma (R.node i.castSucc))).2)
    (hright : ∀ i, u i (R.node i.succ) = ((R.gauge i).lift (gamma (R.node i.succ))).2)
    (w : ∀ i, M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) (R.node i.castSucc) (R.node i.succ))
    (hprimitive : ∀ i s, s ∈ Icc (R.node i.castSucc) (R.node i.succ) →
      (u i s).val = (u i (R.node i.castSucc)).val + ∫ r in R.node i.castSucc..s, w i r) :
    ∃ p : ℕ → M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)),
      Tendsto (fun k => M14BackwardLAction G (p k)) atTop
        (𝓝 (∑ i, gaugeCylinderAction (R.gauge i).index
          (fun s => ((R.gauge i).lift (gamma s)).1) (u i) (w i))) := by
  classical
  have hab (i : Fin R.count) : R.node i.castSucc ≤ R.node i.succ :=
    R.monotone (Fin.castSucc_le_succ i)
  have hchart (i : Fin R.count) : MapsTo (u i) (Icc (R.node i.castSucc) (R.node i.succ))
      (chartAt (EuclideanSpace ℝ (Fin 3)) (R.gauge i).center).source := by
    rw [(G.gaugeCover.spatial (R.gauge i).index).chartAt_source_eq_univ]
    exact mapsTo_univ _ _
  have hcoord (i : Fin R.count) (s : ℝ) :
      extChartAt (𝓡 3) (R.gauge i).center (u i s) = (u i s).val := by
    rw [extChartAt_coe]
    rfl
  choose alpha d hd K hK _ huK halpha hlim hdlim using fun i =>
    M08.smooth_chart_recovery (hab i) (R.gauge i).center (u i) (hu i) (hchart i) (w i)
      (by simpa only [hcoord] using hprimitive i)
  let theta (i : Fin R.count) (s : ℝ) := ((R.gauge i).lift (gamma s)).1
  have htheta (i : Fin R.count) : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (theta i)
      (Icc (R.left i) (R.right i)) :=
    gauge_square_clock_smooth (R.gauge i) gamma T (R.source i)
      (fun s hs => hclock s (R.big_subset i hs))
  have hglobal : R.node 0 < R.node (Fin.last R.count) := by
    rw [R.first, R.last]
    exact Real.sqrt_pos.mpr htau
  have hglue (k : ℕ) := gauge_recoveries_glue R.node R.monotone hglobal gamma hgamma T
    (by simpa only [R.first, R.last] using hclock) R.gauge R.left R.right
    (by simpa only [R.first, R.last] using R.big_subset)
    R.core_subset (by simpa only [R.first, R.last] using R.near) R.source
    (fun i => alpha i k) (fun i => (halpha i k).1)
    (fun i => (halpha i k).2.1.trans (hleft i))
    (fun i => (halpha i k).2.2.1.trans (hright i))
    (fun i => (halpha i k).2.2.2.1.trans (EventuallyEq.of_eq (by rw [hleft i])))
    (fun i => (halpha i k).2.2.2.2.1.trans (EventuallyEq.of_eq (by rw [hright i])))
  choose g hg hpieces hx hy hgclock using hglue
  let v (i : Fin R.count) (k : ℕ) := (hd i k).toLp (d i k)
  have hv (i : Fin R.count) (k : ℕ) :
      (v i k : ℝ → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Icc (R.node i.castSucc) (R.node i.succ))]
          deriv (fun s => (alpha i k s).val) := by
    have hdval (s : ℝ) : HasDerivAt (fun r => (alpha i k r).val) (d i k s) s := by
      convert (halpha i k).2.2.2.2.2.2.2.2 s using 1
      ext r
      rw [Function.comp_apply, extChartAt_coe]
      rfl
    filter_upwards [(hd i k).coeFn_toLp] with s hs
    exact hs.trans (hdval s).deriv.symm
  have hpaths (k : ℕ) := gauge_recovery_path hM12 htau R.node R.monotone R.first R.last
    (g k) (by simpa only [R.first, R.last] using hg k)
    (by simpa only [R.first, R.last] using hgclock k)
    (by simpa only [R.first] using hx k) (by simpa only [R.last] using hy k)
    (fun i => (R.gauge i).index) theta (fun i => alpha i k)
    (fun i => ((htheta i).mono (R.core_subset i)).of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    (fun i => (halpha i k).1.contMDiffOn.of_le (by simp : (1 : ℕ∞ω) ≤ ∞))
    (hpieces k) (fun i => v i k) (fun i => hv i k)
  choose p _ haction using hpaths
  have hlimit (i : Fin R.count) : Tendsto (fun k =>
      gaugeCylinderAction (R.gauge i).index (theta i) (alpha i k) (v i k)) atTop
      (𝓝 (gaugeCylinderAction (R.gauge i).index (theta i) (u i) (w i))) :=
    gauge_cylinder_action_tendsto hM12 (R.gauge i).index (R.gauge i).center
      (hab i) (theta i) ((htheta i).continuousOn.mono (R.core_subset i)) (hK i)
      (alpha i) (u i) (fun k => (halpha i k).1.continuous.continuousOn) (hu i)
      (fun k => (halpha i k).2.2.2.2.2.2.2.1) (huK i) (hlim i)
      (v i) (w i) (hdlim i)
  refine ⟨p, ?_⟩
  simpa only [haction] using tendsto_finsetSum Finset.univ (fun i _ => hlimit i)

end PoincareConjecture.Proofs.M46
