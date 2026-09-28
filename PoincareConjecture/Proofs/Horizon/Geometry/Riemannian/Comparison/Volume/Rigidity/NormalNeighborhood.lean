import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Injectivity.BallDiffeomorphism
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential











noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter Function
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace



theorem exists_normal_neighborhood_of_metricComplete
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) :
    ∃ R : ℝ, 0 < R ∧ ∃ e : EuclideanSpace ℝ (Fin n) → M,
      e 0 = p ∧ ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧
      (∀ u w : EuclideanSpace ℝ (Fin n), g.inner (e 0) (mfderiv (𝓡 n) (𝓡 n) e 0 u)
        (mfderiv (𝓡 n) (𝓡 n) e 0 w) = inner ℝ u w) ∧
      (∀ v ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R}) ∧
      (∀ v ∈ Metric.ball 0 R, Injective (mfderiv (𝓡 n) (𝓡 n) e v)) ∧
      InjOn e (Metric.ball 0 R) ∧
      ∀ r : ℝ, 0 < r → r ≤ R → e '' Metric.ball 0 r = g.ball p r := by
  have hcompact := g.isCompact_closure_ball_of_metricComplete hc p 1
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_radial_exponential_of_precompact_ball p
      (by norm_num : (0 : ℝ) < 1) hcompact
  have hezero : ContMDiffAt (𝓡 n) (𝓡 n) ∞ e 0 :=
    he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simp))
  let c := extChartAt (𝓡 n) p
  let F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) := c ∘ e
  have hc0 : e 0 ∈ c.source := by simpa only [he0] using mem_extChartAt_source p
  have hF : ContDiffAt ℝ ∞ F 0 := contMDiffAt_iff_contDiffAt.mp
    ((contMDiffAt_extChartAt' (by simpa only [c, extChartAt_source] using hc0)).comp 0
      hezero)
  have hFd : HasFDerivAt F L.toContinuousLinearMap 0 := hed
  let H := hF.toOpenPartialHomeomorph F hFd (by simp)
  have h0H : (0 : EuclideanSpace ℝ (Fin n)) ∈ H.source :=
    hF.mem_toOpenPartialHomeomorph_source hFd (by simp)
  have hunit : IsUnit (fderiv ℝ F 0) := by
    rw [hFd.fderiv, ContinuousLinearMap.isUnit_iff_bijective]
    exact L.bijective
  have hnear : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin n)),
      x ∈ Metric.ball 0 1 ∧ x ∈ H.source ∧ e x ∈ c.source ∧
        IsUnit (fderiv ℝ F x) := by
    filter_upwards [Metric.ball_mem_nhds _ (by norm_num : (0 : ℝ) < 1),
      H.open_source.mem_nhds h0H,
      hezero.continuousAt.preimage_mem_nhds
        ((isOpen_extChartAt_source (I := 𝓡 n) p).mem_nhds hc0),
      (hF.continuousAt_fderiv (by simp)).preimage_mem_nhds
        (Units.isOpen.mem_nhds hunit)] with x hx hH hc hunit
    exact ⟨hx, hH, hc, hunit⟩
  obtain ⟨R, hR, hRsub⟩ := Metric.mem_nhds_iff.mp hnear
  have hsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R ⊆ Metric.ball 0 1 :=
    fun x hx => (hRsub hx).1
  have hinj : InjOn e (Metric.ball 0 R) := by
    intro x hx y hy hxy
    apply H.injOn (hRsub hx).2.1 (hRsub hy).2.1
    change F x = F y
    exact congrArg c hxy
  have hdinj : ∀ x ∈ Metric.ball 0 R, Injective (mfderiv (𝓡 n) (𝓡 n) e x) := by
    intro x hx u w huw
    have hd := mfderiv_comp x
      (mdifferentiableAt_extChartAt
        (by simpa only [c, extChartAt_source] using (hRsub hx).2.2.1))
      ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds (hsub hx))).mdifferentiableAt
        (by simp))
    rw [mfderiv_eq_fderiv] at hd
    have hFi := (ContinuousLinearMap.isUnit_iff_bijective.mp (hRsub hx).2.2.2).1
    apply hFi
    change fderiv ℝ (c ∘ e) x u = fderiv ℝ (c ∘ e) x w
    rw [hd]
    exact congrArg (mfderiv (𝓡 n) (𝓡 n) c (e x)) huw
  have hnorm := g.pullbackCoefficients_zero_of_normalized_chart hezero he0 hed hL
  refine ⟨min R 1, lt_min hR (by norm_num), e, he0,
    he.mono (Metric.ball_subset_ball (min_le_right _ _)), hnorm, ?_, ?_,
    hinj.mono (Metric.ball_subset_ball (min_le_left _ _)), ?_⟩
  · intro v hv t ht
    exact (hgeo v (Metric.ball_subset_ball (min_le_right R 1) hv)).1 t
      (Metric.ball_subset_ball (min_le_right R 1) ht)
  · intro v hv
    exact hdinj v (Metric.ball_subset_ball (min_le_left R 1) hv)
  · intro r hr hrR
    have hr1 : r ≤ 1 := hrR.trans (min_le_right _ _)
    have hrsub : Metric.ball (0 : EuclideanSpace ℝ (Fin n)) r ⊆ Metric.ball 0 1 :=
      Metric.ball_subset_ball hr1
    have hcover := Poincare.VolumeComparison.image_localMinimizingSet_eq_ball
      g p (by norm_num : (0 : ℝ) < 1) hcompact L e hL he0 hed
      (fun v hv => (hgeo v hv).1)
    exact (g.image_ball_and_radial_edist_eq_of_injOn p hr hr1 hcover
      (fun v hv => by
        simpa only [one_smul, ENNReal.ofReal_one, mul_one] using
          ((hgeo v (hrsub hv)).2 1 ⟨by norm_num, le_rfl⟩).2)
      (hinj.mono (Metric.ball_subset_ball (hrR.trans (min_le_left _ _))))).1

end PoincareConjecture.RiemannianMetric
