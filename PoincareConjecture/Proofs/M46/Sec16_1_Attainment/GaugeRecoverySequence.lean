import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePrimitivePartition
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryGluing
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeRecoveryPath









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}




theorem gauge_primitive_recovery_sequence (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau)) :
    ∃ p : ℕ → M14BackwardPath G T 0 tau (gamma 0) (gamma (Real.sqrt tau)),
      Tendsto (fun k => M14BackwardLAction G (p k)) atTop (𝓝 R.action) := by
  classical
  have hab (i : Fin R.count) : R.node i.castSucc ≤ R.node i.succ :=
    R.monotone (Fin.castSucc_le_succ i)
  have hsrc (i : Fin R.count) :
      MapsTo gamma (Icc (R.node i.castSucc) (R.node i.succ)) (R.gauge i).source :=
    fun _ hs => R.source i (R.core_subset i hs)
  choose alpha d hd K hK hgammaK halpha hlim hdlim using fun i =>
    gauge_spatial_recovery (R.gauge i) (hab i) gamma hgamma.continuousOn
      (hsrc i) (R.velocity i) (R.primitive i)
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
    (fun i => (halpha i k).2.1) (fun i => (halpha i k).2.2.1)
    (fun i => (halpha i k).2.2.2.1) (fun i => (halpha i k).2.2.2.2.1)
  choose g hg hpieces hx hy hgclock using hglue
  let v (i : Fin R.count) (k : ℕ) := (hd i k).toLp (d i k)
  have hv (i : Fin R.count) (k : ℕ) :
      (v i k : ℝ → EuclideanSpace ℝ (Fin 3))
        =ᵐ[volume.restrict (Icc (R.node i.castSucc) (R.node i.succ))]
          deriv (fun s => (alpha i k s).val) := by
    filter_upwards [(hd i k).coeFn_toLp] with s hs
    exact hs.trans ((halpha i k).2.2.2.2.2.2.2.2 s).deriv.symm
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
      (𝓝 (gaugePieceAction (R.gauge i) gamma (R.velocity i))) := by
    have h := gauge_cylinder_action_tendsto hM12 (R.gauge i).index (R.gauge i).center
      (hab i) (theta i) ((htheta i).continuousOn.mono (R.core_subset i)) (hK i)
      (alpha i) (fun s => ((R.gauge i).lift (gamma s)).2)
      (fun k => (halpha i k).1.continuous.continuousOn)
      ((R.gauge i).smooth.continuousOn.snd.comp hgamma.continuousOn (hsrc i))
      (fun k => (halpha i k).2.2.2.2.2.2.2.1) (hgammaK i) (hlim i)
      (v i) (R.velocity i) (hdlim i)
    rw [gaugeCylinderAction_eq (R.gauge i) gamma (hsrc i) (hab i) (R.velocity i)] at h
    exact h
  refine ⟨p, ?_⟩
  simpa only [haction, GaugePrimitivePartition.action] using
    tendsto_finsetSum Finset.univ (fun i _ => hlimit i)

end PoincareConjecture.Proofs.M46
