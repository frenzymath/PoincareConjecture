import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.FirstCollision











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_collision_at_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) {R C : ℝ}
    (hC : 0 < C) (hCR : C < R)
    (hρC : g.truncatedInjectivityRadius hc C p < C)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hbij : ∀ z ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e z))
    (hgauss : ∀ z ∈ Metric.ball 0 R, ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (e z) (mfderiv (𝓡 n) (𝓡 n) e z z)
        (mfderiv (𝓡 n) (𝓡 n) e z a) = inner ℝ z a) :
    ∃ v w : EuclideanSpace ℝ (Fin n),
      ‖v‖ = g.truncatedInjectivityRadius hc C p ∧
      ‖w‖ = g.truncatedInjectivityRadius hc C p ∧
      v ≠ w ∧ e v = e w ∧
      mfderiv (𝓡 n) (𝓡 n) e v v = -mfderiv (𝓡 n) (𝓡 n) e w w := by
  have hR : 0 < R := hC.trans hCR
  obtain ⟨r, hρr, hrC⟩ := exists_between hρC
  have hrR : r < R := hrC.trans hCR
  have hr : 0 < r := (g.truncatedInjectivityRadius_pos hc hC p).trans hρr
  have hnot : ¬ InjOn e (Metric.closedBall 0 r) := by
    intro hi
    exact (not_le_of_gt hρr) (g.le_truncatedInjectivityRadius_of_radial_exponential
      hc p hR hr.le hrR.le hrC.le L e hL he0 hed hgeo
      (hi.mono Metric.ball_subset_closedBall))
  have hsub : Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 R :=
    Metric.closedBall_subset_ball hrR
  have hlocal (z) (hz : z ∈ Metric.closedBall 0 r) : ∃ U ∈ 𝓝 z, InjOn e U := by
    obtain ⟨b, hb, _, hbe, _, _⟩ :=
      exists_smooth_inverse_branch Metric.isOpen_ball he hbij (hsub hz)
    exact ⟨b.source, b.open_source.mem_nhds hb, b.injOn.congr hbe⟩
  obtain ⟨v, hv, w, hw, heq, hne, _, hmin⟩ :=
    exists_minimal_collision (he.continuousOn.mono hsub) hlocal hnot
  obtain ⟨ev, hvs, _, hev, hvsmooth, hvismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball he hbij (hsub hv)
  obtain ⟨ew, hws, _, hew, hwsmooth, hwismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball he hbij (hsub hw)
  have hvle : ‖v‖ ≤ r := by simpa using hv
  have hwle : ‖w‖ ≤ r := by simpa using hw
  have hnorm := norm_eq_of_minimal_collision hvle hwle heq hne
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hv))).continuousAt)
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hw))).continuousAt)
    ev ew hvs hws hev.symm hew.symm hmin
  have hnormle : ‖v‖ ≤ g.truncatedInjectivityRadius hc C p := by
    apply g.le_truncatedInjectivityRadius_of_radial_exponential hc p hR
      (norm_nonneg v) (hvle.trans hrR.le) (hvle.trans hrC.le) L e hL he0 hed hgeo
    intro x hx y hy hxy
    by_contra hxyne
    have hxlt : ‖x‖ < ‖v‖ := by simpa using hx
    have hylt : ‖y‖ < ‖v‖ := by simpa using hy
    have hbound := hmin x (by simpa using hxlt.le.trans hvle)
      y (by simpa using hylt.le.trans hvle) hxy hxyne
    exact (not_lt_of_ge hbound) ((max_lt hxlt hylt).trans_le (le_max_left _ _))
  have hρle : g.truncatedInjectivityRadius hc C p ≤ ‖v‖ := by
    have h := g.truncatedInjectivityRadius_le_max_of_collision hc hC.le p
      (fun h => hne (L.injective h))
      ((g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo (hsub hv)).trans
        (heq.trans (g.globalExponential_eq_radial_exponential hc p hR L e he0 hed hgeo
          (hsub hw)).symm))
    simpa only [g.tangentNorm_orthonormal_frame p L hL, ← hnorm, max_self] using h
  have hevd (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) ev v a = mfderiv (𝓡 n) (𝓡 n) e v a := by
    have h := (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).mfderiv_eq
      (I := 𝓡 n) (I' := 𝓡 n)
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A a) h
  have hewd (a : EuclideanSpace ℝ (Fin n)) :
      mfderiv (𝓡 n) (𝓡 n) ew w a = mfderiv (𝓡 n) (𝓡 n) e w a := by
    have h := (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).mfderiv_eq
      (I := 𝓡 n) (I' := 𝓡 n)
    exact congrArg (fun A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) => A a) h
  have hreturn := g.radial_velocities_eq_neg_of_minimal_collision hvle hwle heq hne
    ev ew hvs hws hev.symm hew.symm hvsmooth hwsmooth hvismooth hwismooth
    (by intro a; rw [hevd, hevd]; exact hgauss v (hsub hv) a)
    (by intro a; rw [hewd, hewd, heq]; exact hgauss w (hsub hw) a) hmin
  exact ⟨v, w, le_antisymm hnormle hρle,
    hnorm.symm.trans (le_antisymm hnormle hρle), hne, heq,
    (hevd v).symm.trans (hreturn.trans (congrArg Neg.neg (hewd w)))⟩



theorem exists_inverse_branches_at_truncatedInjectivityRadius
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) {R C : ℝ}
    (hC : 0 < C) (hCR : C < R)
    (hρC : g.truncatedInjectivityRadius hc C p < C)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w)
    (he0 : e 0 = p)
    (hed : HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v)) L.toContinuousLinearMap 0)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R})
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hbij : ∀ z ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) e z))
    (hgauss : ∀ z ∈ Metric.ball 0 R, ∀ a : EuclideanSpace ℝ (Fin n),
      g.inner (e z) (mfderiv (𝓡 n) (𝓡 n) e z z)
        (mfderiv (𝓡 n) (𝓡 n) e z a) = inner ℝ z a) :
    ∃ v w : EuclideanSpace ℝ (Fin n),
      ∃ ev ew : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M,
      ‖v‖ = g.truncatedInjectivityRadius hc C p ∧
      ‖w‖ = g.truncatedInjectivityRadius hc C p ∧ v ≠ w ∧ e v = e w ∧
      v ∈ ev.source ∧ w ∈ ew.source ∧
      ev.source ⊆ Metric.ball 0 R ∧ ew.source ⊆ Metric.ball 0 R ∧
      EqOn ev e ev.source ∧ EqOn ew e ew.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ev ev.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ew ew.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ev.symm ev.target ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ ew.symm ew.target ∧
      mfderiv (𝓡 n) (𝓡 n) ev v v = -mfderiv (𝓡 n) (𝓡 n) ew w w := by
  obtain ⟨v, w, hv, hw, hne, heq, hvel⟩ :=
    g.exists_collision_at_truncatedInjectivityRadius hc p hC hCR hρC
      L e hL he0 hed hgeo he hbij hgauss
  have hvR : v ∈ Metric.ball 0 R := by simpa [hv] using hρC.trans hCR
  have hwR : w ∈ Metric.ball 0 R := by simpa [hw] using hρC.trans hCR
  obtain ⟨ev, hvs, hsubv, hev, hvsmooth, hvismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball he hbij hvR
  obtain ⟨ew, hws, hsubw, hew, hwsmooth, hwismooth⟩ :=
    exists_smooth_inverse_branch Metric.isOpen_ball he hbij hwR
  refine ⟨v, w, ev, ew, hv, hw, hne, heq, hvs, hws, hsubv, hsubw,
    hev, hew, hvsmooth, hwsmooth, hvismooth, hwismooth, ?_⟩
  have hdv := (hev.eventuallyEq_of_mem (ev.open_source.mem_nhds hvs)).mfderiv_eq
    (I := 𝓡 n) (I' := 𝓡 n)
  have hdw := (hew.eventuallyEq_of_mem (ew.open_source.mem_nhds hws)).mfderiv_eq
    (I := 𝓡 n) (I' := 𝓡 n)
  rw [hdv, hdw]
  exact hvel

end PoincareConjecture.RiemannianMetric
