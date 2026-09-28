import PoincareConjecture.Proofs.M46.Sec16_1_Attainment.GaugePartition
import PoincareConjecture.Proofs.M08.PathRecovery
import PoincareConjecture.Proofs.M14.Sec6_2_IntervalLift
import PoincareConjecture.Proofs.M14.Mathlib.OpenSubsetChart










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology intervalIntegral

universe u

namespace PoincareConjecture.Proofs.M46

variable {X : Type u} [TopologicalSpace X] {time : X → ℝ}
  {I : SpacetimeInterval} {G : GeneralizedLGeometryTransport 3 X time I}





theorem gauge_spatial_recovery (e : AttainmentGauge G) {a b : ℝ} (hab : a ≤ b)
    (gamma : ℝ → G.Point) (hgamma : ContinuousOn gamma (Icc a b))
    (hsrc : MapsTo gamma (Icc a b) e.source)
    (w : M08.ChartL2 (EuclideanSpace ℝ (Fin 3)) a b)
    (hprimitive : ∀ s ∈ Icc a b,
      (e.lift (gamma s)).2.val = (e.lift (gamma a)).2.val + ∫ r in a..s, w r) :
    ∃ (alpha : ℕ → ℝ → G.gaugeCover.spatial e.index)
      (d : ℕ → ℝ → EuclideanSpace ℝ (Fin 3))
      (hd : ∀ k, MemLp (d k) 2 (volume.restrict (Icc a b)))
      (K : Set (G.gaugeCover.spatial e.index)),
      IsCompact K ∧ MapsTo (fun s => (e.lift (gamma s)).2) (Icc a b) K ∧
      (∀ k, ContMDiff (𝓘(ℝ, ℝ)) (𝓡 3) ∞ (alpha k) ∧
        alpha k a = (e.lift (gamma a)).2 ∧ alpha k b = (e.lift (gamma b)).2 ∧
        (alpha k =ᶠ[𝓝 a] fun _ => (e.lift (gamma a)).2) ∧
        (alpha k =ᶠ[𝓝 b] fun _ => (e.lift (gamma b)).2) ∧
        (∀ s, s ≤ a → alpha k s = (e.lift (gamma a)).2) ∧
        (∀ s, b ≤ s → alpha k s = (e.lift (gamma b)).2) ∧
        MapsTo (alpha k) (Icc a b) K ∧
        ∀ s, HasDerivAt (fun r => (alpha k r).val) (d k s) s) ∧
      TendstoUniformlyOn alpha (fun s => (e.lift (gamma s)).2) atTop (Icc a b) ∧
      Tendsto (fun k => (hd k).toLp (d k)) atTop (𝓝 w) := by
  have hspatial : ContinuousOn (fun s => (e.lift (gamma s)).2) (Icc a b) :=
    e.smooth.continuousOn.snd.comp hgamma hsrc
  have hchart : MapsTo (fun s => (e.lift (gamma s)).2) (Icc a b)
      (chartAt (EuclideanSpace ℝ (Fin 3)) e.center).source := by
    rw [(G.gaugeCover.spatial e.index).chartAt_source_eq_univ]
    exact mapsTo_univ _ _
  have hcoord (s : ℝ) :
      extChartAt (𝓡 3) e.center (e.lift (gamma s)).2 = (e.lift (gamma s)).2.val := by
    rw [extChartAt_coe]
    rfl
  obtain ⟨alpha, d, hd, K, hK, _, hgammaK, halpha, hlim, hdlim⟩ :=
    M08.smooth_chart_recovery hab e.center (fun s => (e.lift (gamma s)).2)
      hspatial hchart w (by simpa only [hcoord] using hprimitive)
  refine ⟨alpha, d, hd, K, hK, hgammaK, ?_, hlim, hdlim⟩
  intro k
  obtain ⟨hsmooth, ha, hb, hga, hgb, hleft, hright, hmap, hderiv⟩ := halpha k
  refine ⟨hsmooth, ha, hb, hga, hgb, hleft, hright, hmap, ?_⟩
  intro s
  convert hderiv s using 1
  ext r
  rw [Function.comp_apply, extChartAt_coe]
  rfl




theorem gauge_square_clock_smooth (e : AttainmentGauge G) (gamma : ℝ → G.Point)
    (T : ℝ) {C : Set ℝ} (hsrc : MapsTo gamma C e.source)
    (hclock : ∀ s ∈ C, G.spacetime.timeFunction (gamma s) = T - s ^ 2) :
    ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡∂ 1) ∞ (fun s => (e.lift (gamma s)).1) C := by
  apply M14.intervalLift_contMDiffOn (𝓘(ℝ, ℝ))
    (G.timeIntervals.interval (G.gaugeCover.interval e.index))
  have heq (s : ℝ) (hs : s ∈ C) : (e.lift (gamma s)).1.val = T - s ^ 2 :=
    (e.clock (gamma s) (hsrc hs)).trans (hclock s hs)
  exact ((contDiff_const.sub (contDiff_id.pow 2)).contMDiff.contMDiffOn).congr heq




theorem gauge_recovery_lift (e : AttainmentGauge G) {a b : ℝ} (hab : a ≤ b)
    (gamma : ℝ → G.Point) (T : ℝ) (hsrc : MapsTo gamma (Icc a b) e.source)
    (hclock : ∀ s ∈ Icc a b, G.spacetime.timeFunction (gamma s) = T - s ^ 2)
    (alpha : ℝ → G.gaugeCover.spatial e.index)
    (halpha : ContMDiffOn (𝓘(ℝ, ℝ)) (𝓡 3) ∞ alpha (Icc a b))
    (ha : alpha a = (e.lift (gamma a)).2) (hb : alpha b = (e.lift (gamma b)).2) :
    let beta := fun s => (G.gaugeCover.cylinder e.index).toSpacetime
      ((e.lift (gamma s)).1, alpha s)
    ContMDiffOn (𝓘(ℝ, ℝ)) (spacetimeModel 3) ∞ beta (Icc a b) ∧
      (∀ s ∈ Icc a b, G.spacetime.timeFunction (beta s) = T - s ^ 2) ∧
      beta a = gamma a ∧ beta b = gamma b := by
  have ht := gauge_square_clock_smooth e gamma T hsrc hclock
  refine ⟨(G.gaugeCover.cylinder e.index).smooth.comp_contMDiffOn
    (ht.prodMk halpha), ?_, ?_, ?_⟩
  · intro s hs
    rw [(G.gaugeCover.cylinder e.index).time_eq]
    exact (e.clock (gamma s) (hsrc hs)).trans (hclock s hs)
  · simp only [ha]
    exact e.right_inv (gamma a) (hsrc ⟨le_rfl, hab⟩)
  · simp only [hb]
    exact e.right_inv (gamma b) (hsrc ⟨hab, le_rfl⟩)

end PoincareConjecture.Proofs.M46
