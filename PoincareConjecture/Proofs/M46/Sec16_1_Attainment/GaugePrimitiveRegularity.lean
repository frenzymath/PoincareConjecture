import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugeWeakRegularity
import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePieceMinimum









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}



theorem gauge_primitive_piece_contMDiffOn (hM12 : GeneralizedRicciGaugeTheory.{u} 3)
    {T tau : ℝ} (htau : 0 < tau) (gamma : ℝ → G.Point) (hgamma : Continuous gamma)
    (hclock : ∀ s ∈ Icc 0 (Real.sqrt tau),
      G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (R : GaugePrimitivePartition gamma 0 (Real.sqrt tau))
    (hfinite : M14FiniteValueDomain G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (hmin : R.action ≤ M14ActionValue G T 0 tau (gamma 0) (gamma (Real.sqrt tau)))
    (j : Fin R.count) (hj : R.node j.castSucc < R.node j.succ) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ gamma
      (Icc (R.node j.castSucc) (R.node j.succ)) := by
  let e := R.gauge j
  let theta (s : ℝ) := (e.lift (gamma s)).1
  let alpha (s : ℝ) := (e.lift (gamma s)).2
  have hsrc : MapsTo gamma (Icc (R.node j.castSucc) (R.node j.succ)) e.source :=
    fun _ hs => R.source j (R.core_subset j hs)
  have htheta : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ theta
      (Icc (R.node j.castSucc) (R.node j.succ)) :=
    (gauge_square_clock_smooth e gamma T (R.source j)
      (fun s hs => hclock s (R.big_subset j hs))).mono (R.core_subset j)
  have hthetaClock (s : ℝ) (hs : s ∈ Icc (R.node j.castSucc) (R.node j.succ)) :
      (theta s).val = T - s ^ 2 :=
    (e.clock (gamma s) (hsrc hs)).trans (hclock s (R.big_subset j (R.core_subset j hs)))
  have halpha : ContinuousOn alpha (Icc (R.node j.castSucc) (R.node j.succ)) :=
    e.smooth.continuousOn.snd.comp hgamma.continuousOn hsrc
  have hreg := gauge_cylinder_minimum_contDiffOn hM12 e.index e.center hj theta htheta
    hthetaClock alpha halpha (R.velocity j) (R.primitive j)
    (fun beta hbeta hleft hright v hprimitive =>
      gauge_piece_minimum hM12 htau gamma hgamma hclock R hfinite hmin j beta hbeta
        hleft hright v hprimitive)
  have hspatial : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) ∞ alpha
      (Icc (R.node j.castSucc) (R.node j.succ)) := by
    have hc := (contMDiffOn_chart_symm (I := 𝓡 3) (x := e.center) (n := ∞)).comp
      hreg.contMDiffOn (fun s _ => by
        rw [(G.gaugeCover.spatial e.index).chartAt_target_eq]
        exact (alpha s).property)
    apply hc.congr
    intro s _
    exact ((G.gaugeCover.spatial e.index).chartAt_symm_apply_val e.center (alpha s)).symm
  have hcurve := (G.gaugeCover.cylinder e.index).smooth.comp_contMDiffOn (htheta.prodMk hspatial)
  apply hcurve.congr
  intro s hs
  exact (e.right_inv (gamma s) (hsrc hs)).symm

end PoincareConjecture.Proofs.M46
