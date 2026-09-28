import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.Radius.Exponential
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.FlatMetric
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Composition








noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem contMDiff_and_pullbackCoefficients_globalExponential_of_flat
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    (hc : MetricComplete g) (hflat : ∀ x, D.curvatureTensorNorm x = 0) (p : M)
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (hL : ∀ v w, g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
      (extChartAt (𝓡 n) p p) (L v) (L w) = inner ℝ v w) :
    let e := fun v => g.globalExponential hc p (L v)
    ContMDiff (𝓡 n) (𝓡 n) ∞ e ∧
      ∀ v, g.pullbackCoefficients e v = innerSL ℝ := by
  dsimp only
  let e := fun v => g.globalExponential hc p (L v)
  have hlocal (x : EuclideanSpace ℝ (Fin n)) :
      ContMDiffAt (𝓡 n) (𝓡 n) ∞ e x ∧
        g.pullbackCoefficients e x = innerSL ℝ := by
    let R := ‖x‖ + 1
    have hR : 0 < R := by dsimp [R]; positivity
    have hx : x ∈ Metric.ball 0 R := by simp [Metric.mem_ball, R]
    obtain ⟨K, q, hK, hq, hq0, hqd, hgeo⟩ :=
      g.exists_orthonormal_radial_exponential_of_metricComplete hc p hR
    let A := L.trans K.symm
    have hAinner (u w : EuclideanSpace ℝ (Fin n)) :
        inner ℝ (A u) (A w) = inner ℝ u w := by
      rw [← hK]
      simpa only [A, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply] using hL u w
    have hAnorm (u : EuclideanSpace ℝ (Fin n)) : ‖A u‖ = ‖u‖ := by
      have h := g.tangentNorm_orthonormal_frame p K hK (A u)
      have h' : g.tangentNorm p (L u) = ‖A u‖ := by
        simpa only [A, ContinuousLinearEquiv.trans_apply,
          ContinuousLinearEquiv.apply_symm_apply] using h
      exact h'.symm.trans (g.tangentNorm_orthonormal_frame p L hL u)
    have hAx : A x ∈ Metric.ball 0 R := by
      simpa only [Metric.mem_ball, dist_zero_right, hAnorm] using hx
    have heq : q ∘ A =ᶠ[𝓝 x] e := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
      have hAy : A y ∈ Metric.ball 0 R := by
        simpa only [Metric.mem_ball, dist_zero_right, hAnorm] using hy
      have h := g.globalExponential_eq_radial_exponential hc p hR K q hq0 hqd
        (fun v hv => (hgeo v hv).1) hAy
      simpa only [Function.comp_apply, A, ContinuousLinearEquiv.trans_apply,
        ContinuousLinearEquiv.apply_symm_apply, e] using h.symm
    have hqAt := hq.contMDiffAt (Metric.isOpen_ball.mem_nhds hAx)
    have hAAt : ContMDiffAt (𝓡 n) (𝓡 n) ∞ A x :=
      contMDiffAt_iff_contDiffAt.mpr A.contDiff.contDiffAt
    refine ⟨(hqAt.comp x hAAt).congr_of_eventuallyEq heq.symm, ?_⟩
    have hzero : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 R := by
      simpa only [Metric.mem_ball, dist_self] using hR
    have hnorm : ∀ u w, g.pullbackCoefficients q 0 u w = inner ℝ u w :=
      g.pullbackCoefficients_zero_of_orthonormal p
        (hq.contMDiffAt (Metric.isOpen_ball.mem_nhds hzero)) hq0 hqd hK
    have hpull := g.pullbackCoefficients_eq_innerSL_of_flat_radial D hq hnorm
      (fun v hv => (hgeo v hv).1) hAx
      (fun t _ => hflat (q (t • A x)))
      (fun t ht => ((hgeo (A x) hAx).2 t ht).1)
    ext u w
    have hcomp := g.pullbackCoefficients_comp_of_eventuallyEq
      (hqAt.mdifferentiableAt (by simp)) A.differentiableAt heq u w
    rw [A.hasFDerivAt.fderiv, hpull] at hcomp
    exact hcomp.symm.trans (hAinner u w)
  exact ⟨fun x => (hlocal x).1, fun x => (hlocal x).2⟩

end PoincareConjecture.RiemannianMetric
