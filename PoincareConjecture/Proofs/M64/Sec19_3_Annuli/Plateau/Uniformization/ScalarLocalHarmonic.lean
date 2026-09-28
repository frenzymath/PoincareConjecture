import PoincareConjecture.Proofs.M60.Lemma18_10_LeastSphere.UniformizationIsothermal
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.NormalizedChart
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Surface.Norm

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.M64Uniformization

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem exists_local_annular_gauss_metric (g : RiemannianMetric 2 Plane) (p : Plane) :
    ∃ (e : OpenPartialHomeomorph Plane Plane) (R : ℝ)
      (G : RiemannianMetric 2 Plane) (_DG : LeviCivitaData G),
      0 < R ∧ Metric.ball 0 R ⊆ e.source ∧ e 0 = p ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e e.source ∧
      ContMDiffOn (𝓡 2) (𝓡 2) ∞ e.symm e.target ∧
      (∀ x ∈ Metric.ball 0 R, G.euclideanCoefficients x = g.pullbackCoefficients e x) ∧
      (∀ x ∈ Metric.ball 0 R, ∀ v : Plane,
        (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ G.euclideanCoefficients x v v ∧
          G.euclideanCoefficients x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2) ∧
      ∀ x w : Plane, G.euclideanCoefficients x x w = inner ℝ x w := by
  obtain ⟨e, he0, hep, he, hei, hgauss, hB0, -⟩ :=
    g.exists_normalized_exponential_chart_firstJet p
  let B₀ : Plane →L[ℝ] Plane →L[ℝ] ℝ := innerSL ℝ
  have hBc := (g.contDiffAt_pullbackCoefficients
    (he.contMDiffAt (e.open_source.mem_nhds he0))).continuousAt
  have hnear : ∀ᶠ x in 𝓝 (0 : Plane), ‖g.pullbackCoefficients e x - B₀‖ < 1 / 2 := by
    have h := hBc.eventually (Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1 / 2))
    simpa only [Metric.mem_ball, dist_eq_norm, hB0, B₀] using h
  obtain ⟨s, hs, hsmall⟩ := Metric.mem_nhds_iff.mp
    (inter_mem (e.open_source.mem_nhds he0) hnear)
  have hsub : Metric.ball (0 : Plane) s ⊆ e.source := fun x hx => (hsmall hx).1
  have hB : ContDiffOn ℝ ∞ (g.pullbackCoefficients e) (Metric.ball 0 s) :=
    fun x hx => (g.contDiffAt_pullbackCoefficients
      (he.contMDiffAt (e.open_source.mem_nhds (hsub hx)))).contDiffWithinAt
  have hbound (x : Plane) (hx : x ∈ Metric.ball 0 s) (v : Plane) :
      (1 / 4 : ℝ) * ‖v‖ ^ 2 ≤ g.pullbackCoefficients e x v v ∧
        g.pullbackCoefficients e x v v ≤ (9 / 4 : ℝ) * ‖v‖ ^ 2 := by
    have hn := (g.pullbackCoefficients e x - B₀).le_opNorm₂ v v
    change |g.pullbackCoefficients e x v v - inner ℝ v v| ≤
      ‖g.pullbackCoefficients e x - B₀‖ * ‖v‖ * ‖v‖ at hn
    rw [real_inner_self_eq_norm_sq] at hn
    have herr : |g.pullbackCoefficients e x v v - ‖v‖ ^ 2| ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
      hn.trans (by
        calc
          _ = ‖g.pullbackCoefficients e x - B₀‖ * ‖v‖ ^ 2 := by ring
          _ ≤ (1 / 2 : ℝ) * ‖v‖ ^ 2 :=
            mul_le_mul_of_nonneg_right (hsmall hx).2.le (sq_nonneg _))
    constructor <;> nlinarith [abs_le.mp herr, sq_nonneg ‖v‖]
  obtain ⟨G, DG, heq, hglobal⟩ := CoordinateExponential.exists_gauss_metric_extension
    (by positivity : 0 < s / 2) (by linarith : s / 2 < 3 * s / 4)
    (by linarith : 3 * s / 4 < s) (g.pullbackCoefficients e) hB
    (fun _ _ v w => g.symm _ _ _)
    (fun x hx v hv => (mul_pos (by norm_num : (0 : ℝ) < 1 / 4)
      (sq_pos_of_pos (norm_pos_iff.mpr hv))).trans_le (hbound x hx v).1)
    (fun x hx w => hgauss x (hsub hx) w)
  have hhalf : Metric.ball (0 : Plane) (s / 2) ⊆ Metric.ball 0 s :=
    Metric.ball_subset_ball (by linarith)
  refine ⟨e, s / 2, G, DG, by positivity, hhalf.trans hsub, hep, he, hei,
    fun x hx => heq x (Metric.ball_subset_closedBall hx), ?_, hglobal⟩
  intro x hx v
  rw [heq x (Metric.ball_subset_closedBall hx)]
  exact hbound x (hhalf hx) v

theorem exists_local_annular_harmonic_chart (g : RiemannianMetric 2 Plane) (p : Plane) :
    ∃ (e : Plane → Plane) (r : ℝ) (h : RiemannianMetric 2 Plane) (Dh : LeviCivitaData h),
      0 < r ∧ e 0 = p ∧ ContMDiffOn (𝓡 2) (𝓡 2) ∞ e (Metric.ball 0 r) ∧
      (∀ x ∈ Metric.ball 0 r, (mfderiv (𝓡 2) (𝓡 2) e x).IsInvertible) ∧
      (∀ x ∈ Metric.ball 0 r, h.euclideanCoefficients x = g.pullbackCoefficients e x) ∧
      ∀ x ∈ Metric.ball 0 r, ∀ i : Fin 2,
        Dh.laplacian (fun y : Plane => y i) x = 0 := by
  obtain ⟨e, R, G, DG, hR, hsource, hep, he, -, hmetric, hell, hgauss⟩ :=
    exists_local_annular_gauss_metric g p
  obtain ⟨K, hK, hcurv⟩ := DG.exists_pos_curvatureTensorNorm_le_on_surface
    (isCompact_closedBall (0 : Plane) R)
  obtain ⟨r, C, H, hr, -, -, hproducer⟩ :=
    RiemannianMetric.exists_uniform_harmonic_radius (by norm_num : 2 ≤ 2) hR hK.le
  obtain ⟨F, hmap⟩ := hproducer G DG hell hgauss
    (fun x hx => hcurv x (Metric.ball_subset_closedBall hx))
  let E : Plane → Plane := e ∘ F.e
  have hEs : ContMDiffOn (𝓡 2) (𝓡 2) ∞ E (Metric.ball 0 (2 * r)) :=
    he.comp F.he (fun x hx => hsource (hmap hx))
  have hEpull (x : Plane) (hx : x ∈ Metric.ball 0 (2 * r)) :
      F.h.euclideanCoefficients x = g.pullbackCoefficients E x := by
    ext v w
    rw [F.hpullback x hx]
    have hexs := he.contMDiffAt (e.open_source.mem_nhds (hsource (hmap hx)))
    have hexd := hexs.mdifferentiableAt (by simp)
    have hFxd := (contMDiffOn_iff_contDiffOn.mp F.he).contDiffAt
      (Metric.isOpen_ball.mem_nhds hx) |>.differentiableAt (by simp)
    rw [← g.pullbackCoefficients_comp_of_eventuallyEq hexd hFxd
      (Filter.EventuallyEq.rfl : (e : Plane → Plane) ∘ F.e =ᶠ[𝓝 x] E) v w]
    change G.inner (F.e x) (mfderiv (𝓡 2) (𝓡 2) F.e x v)
      (mfderiv (𝓡 2) (𝓡 2) F.e x w) = _
    rw [mfderiv_eq_fderiv]
    change G.euclideanCoefficients (F.e x) (fderiv ℝ F.e x v) (fderiv ℝ F.e x w) = _
    rw [hmetric _ (hmap hx)]
  refine ⟨E, 2 * r, F.h, F.D', by positivity, ?_, hEs, ?_, hEpull, F.hharmonic⟩
  · change e (F.e 0) = p
    rw [F.he0, hep]
  · intro x hx
    apply g.isInvertible_mfderiv_of_positive_pullback
    intro v hv
    rw [← hEpull x hx]
    exact F.h.pos x v hv

end PoincareConjecture.M64Uniformization
