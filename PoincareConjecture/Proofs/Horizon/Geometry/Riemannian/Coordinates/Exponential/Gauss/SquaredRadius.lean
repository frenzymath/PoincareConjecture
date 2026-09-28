import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.Gauss.Manifold
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.Gradient
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.ScalarOperators.Locality
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.NormalBall
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Compactness.IntrinsicMetric

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem gradient_squared_radius_of_gauss (g : RiemannianMetric n M) (p : M)
    (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source)
    (hei : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ e.source)
    (hgauss : ∀ w : EuclideanSpace ℝ (Fin n),
      g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v v)
        (mfderiv (𝓡 n) (𝓡 n) e v w) = g.inner p v w)
    {f : M → ℝ} (hf : ContMDiffAt (𝓡 n) 𝓘(ℝ, ℝ) ∞ f (e v))
    (heq : (f ∘ e) =ᶠ[𝓝 v] (fun w => g.inner p w w)) :
    g.gradient f (e v) = mfderiv (𝓡 n) (𝓡 n) e v ((2 : ℝ) • v) := by
  let E := EuclideanSpace ℝ (Fin n)
  have hed : e.MDifferentiable (𝓡 n) (𝓡 n) := ⟨
    fun y hy => (he y hy).mdifferentiableWithinAt (by simp),
    fun y hy => (hei y hy).mdifferentiableWithinAt (by simp)⟩
  have hinv : (mfderiv (𝓡 n) (𝓡 n) e v).IsInvertible := ⟨hed.mfderiv hv, rfl⟩
  apply (g.inner_isInvertible (e v)).injective
  ext z
  let w := (mfderiv (𝓡 n) (𝓡 n) e v).inverse z
  have hw : mfderiv (𝓡 n) (𝓡 n) e v w = z := hinv.self_apply_inverse z
  have hd := congrArg (fun L => L w) (Poincare.mvfderiv_eq_of_eventuallyEq heq)
  rw [mvfderiv_comp v (hf.mdifferentiableAt (by simp)) (hed.mdifferentiableAt hv)] at hd
  simp only [ContinuousLinearMap.comp_apply, hw] at hd
  have hquad : fderiv ℝ (fun y : E => g.inner p y y) v w = 2 * g.inner p v w := by
    have h := ((g.inner p : E →L[ℝ] E →L[ℝ] ℝ).hasFDerivAt).clm_apply
      (hasFDerivAt_id v)
    dsimp only [id] at h
    trans g.inner p v w + g.inner p w v
    · exact congrArg (fun A : E →L[ℝ] ℝ => A w) h.fderiv
    rw [g.symm p w v]
    ring
  have hquad' : mvfderiv (𝓡 n) (fun y : E => g.inner p y y) v w =
      2 * g.inner p v w := by
    simp +instances only [mvfderiv, mfderiv_eq_fderiv, NormedSpace.fromTangentSpace]
    exact hquad
  rw [hquad'] at hd
  rw [g.inner_gradient, ← hw, map_smul, map_smul, smul_apply, smul_eq_mul, hgauss]
  rw [← hw] at hd
  exact hd

theorem exists_radial_chart_of_squared_distance_gradient [T3Space M]
    [PreconnectedSpace M] (g : RiemannianMetric n M) (p : M)
    {f : M → ℝ} (hf : ContMDiff (𝓡 n) 𝓘(ℝ, ℝ) ∞ f)
    {X : (y : M) → TangentSpace (𝓡 n) y}
    (hpotential : f =ᶠ[𝓝 p] (fun y => (g.edist y p).toReal ^ 2))
    (hfield : ∀ᶠ y in 𝓝 p, X y = (1 / 2 : ℝ) • g.gradient f y) :
    ∃ (e : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin n)) M) (r : ℝ),
      0 < r ∧ e 0 = p ∧ Metric.ball 0 r ⊆ e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e e.source ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e.symm e.target ∧
      ∀ v ∈ Metric.ball 0 r,
        X (e v) = mfderiv (𝓡 n) (𝓡 n) e v v := by
  let := g.toMetricSpace
  let E := EuclideanSpace ℝ (Fin n)
  obtain ⟨e, h0, he0, he, hei, hgauss, _⟩ := g.exists_exponential_chart_gauss p
  obtain ⟨a, ha, hsource, hdist⟩ :=
    g.exists_tangentBall_edist_eq_of_gauss p e h0 he0 he hei hgauss
  have hnorm : Continuous (fun v : E => g.tangentNorm p v) := by
    unfold tangentNorm
    exact Real.continuous_sqrt.comp
      ((continuous_const.clm_apply continuous_id).clm_apply continuous_id)
  have hsmall : ∀ᶠ v : E in 𝓝 0, g.tangentNorm p v < a :=
    (isOpen_lt hnorm continuous_const).mem_nhds (by simpa [tangentNorm] using ha)
  have hecont : Tendsto e (𝓝 0) (𝓝 p) := by
    simpa only [ContinuousAt, he0] using e.continuousAt h0
  have hquad : (f ∘ e) =ᶠ[𝓝 (0 : E)] (fun v => g.inner p v v) := by
    filter_upwards [hsmall, hecont.eventually hpotential] with v hv heq
    change f (e v) = _
    rw [heq]
    have hd : (g.edist (e v) p).toReal = g.tangentNorm p v := by
      change dist (e v) p = _
      rw [dist_comm, g.toMetricSpace_dist, hdist v hv]
      exact ENNReal.toReal_ofReal (Real.sqrt_nonneg _)
    rw [hd]
    exact Real.sq_sqrt (by
      by_cases hv0 : v = 0
      · simp [hv0]
      · exact (g.pos p v hv0).le)
  have hdata : {v : E | v ∈ e.source ∧
      X (e v) = (1 / 2 : ℝ) • g.gradient f (e v) ∧
      f (e v) = g.inner p v v} ∈ 𝓝 0 := by
    filter_upwards [e.open_source.mem_nhds h0, hecont.eventually hfield, hquad]
      with v hv hX hq
    exact ⟨hv, hX, hq⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hdata
  refine ⟨e, r, hr, he0, fun v hv => (hball hv).1, he, hei, ?_⟩
  intro v hv
  have heq : (f ∘ e) =ᶠ[𝓝 v] (fun w => g.inner p w w) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hv] with w hw
    exact (hball hw).2.2
  rw [(hball hv).2.1,
    g.gradient_squared_radius_of_gauss p e he hei (hball hv).1
      (hgauss v (hball hv).1) (hf _) heq, map_smul, smul_smul]
  norm_num

end PoincareConjecture.RiemannianMetric
