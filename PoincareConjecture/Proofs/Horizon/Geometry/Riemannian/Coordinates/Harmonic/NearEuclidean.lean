import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Exponential.JetBounds.PrecompactDifferential









noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle

namespace PoincareConjecture.RiemannianMetric

open ConnectionVariation ConnectionAlongCurve

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem radial_geodesic_differential_norm_error
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R K : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) ≤ K)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    (w : EuclideanSpace ℝ (Fin n)) :
    |g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) - ‖w‖| ≤
      ((K * ‖v‖ ^ 2) * Real.exp (max 1 (K * ‖v‖ ^ 2)) / 6) * ‖w‖ := by
  let γ : ℝ → M := fun t => e (t • v)
  let J : (t : ℝ) → TangentSpace (𝓡 n) (γ t) :=
    fun t => mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (t • (v + s • w))) 0 1
  obtain ⟨S, a, hS, h0, ha, hvelocity, hdomain⟩ :=
    exists_open_radial_variation_domain hv w
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-a) a := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓡 n) ∞
      (fun z : ℝ × ℝ => e (z.2 • (v + z.1 • w))) (S ×ˢ Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · exact fun z hz => hdomain z.1 hz.1 z.2 hz.2
  have hvariation : ∀ s ∈ S,
      g.IsGeodesicOn (fun t : ℝ => e (t • (v + s • w))) (Ioo (-a) a) := by
    intro s hs t ht
    exact hgeo _ (hvelocity s hs) t (hdomain s hs t ht)
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 n) ∞ γ (Ioo (-a) a) := by
    apply he.comp
    · apply contMDiffOn_iff_contDiffOn.mpr
      fun_prop
    · intro t ht
      change t • v ∈ Metric.ball 0 R
      simpa only [zero_smul, add_zero] using hdomain 0 h0 t ht
  have hJ : ∀ t ∈ Ioo (-a) a, ContDiffAt ℝ ∞ (chartField γ (γ t) J) t := by
    intro t ht
    apply radialVariation_contDiffAt_chartField Metric.isOpen_ball he v w
    simpa only [zero_smul, add_zero] using hdomain 0 h0 t ht
  have hjac : ∀ t ∈ Ioo (-a) a,
      manifoldCovDerivAlong g γ (manifoldCovDerivAlong g γ J 1) 1 t =
        -D.curvature (γ t) (J t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1)
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) := by
    intro t ht
    have hj := manifoldVariation_jacobi g D hS isOpen_Ioo h0 hsmooth hvariation ht
    dsimp only at hj
    rw [show v + (0 : ℝ) • w = v by simp] at hj
    exact eq_neg_of_add_eq_zero_left hj
  have hJ0 : J 0 = 0 := radialVariation_field_zero e v w
  obtain ⟨P, hP0, hPi, hP, hpair, hbound⟩ :=
    ManifoldJacobi.manifold_jacobi_estimates D (by norm_num : (0 : ℝ) < 1)
      isOpen_Ioo hγ hJ hsub hjac hK hc hJ0
  have hR : 0 < R := (norm_nonneg v).trans_lt (by simpa using hv)
  have hinit := g.radialVariation_initial_tangentNorm
    (he.contMDiffAt (Metric.isOpen_ball.mem_nhds (by simpa using hR))) hnorm v w
  have hend := radialVariation_field_one v w
    ((he.contMDiffAt (Metric.isOpen_ball.mem_nhds hv)).mdifferentiableAt (by simp))
  change g.tangentNorm (γ 0) (manifoldCovDerivAlong g γ J 1 0) = ‖w‖ at hinit
  change J 1 = mfderiv (𝓡 n) (𝓡 n) e v w at hend
  have hone : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := by simp
  have htransport : g.tangentNorm (γ 0) ((P 1).inverse (J 1)) =
      g.tangentNorm (γ 1) (J 1) := by
    have hp := hpair 1 hone ((P 1).inverse (J 1)) ((P 1).inverse (J 1))
    rw [(hPi 1 hone).self_apply_inverse] at hp
    exact congrArg Real.sqrt hp.symm
  have hreverse :
      |g.tangentNorm (γ 0) ((P 1).inverse (J 1)) -
        g.tangentNorm (γ 0) (manifoldCovDerivAlong g γ J 1 0)| ≤
      g.tangentNorm (γ 0)
        ((show TangentSpace (𝓡 n) (γ 0) from (P 1).inverse (J 1)) -
          manifoldCovDerivAlong g γ J 1 0) := by
    let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    have hn (u : TangentSpace (𝓡 n) (γ 0)) : g.tangentNorm (γ 0) u = ‖u‖ := by
      change Real.sqrt (inner ℝ u u) = ‖u‖
      rw [real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    simp only [hn]
    exact abs_norm_sub_norm_le _ _
  have hrem := (hbound 1 hone).1
  simp only [mul_one, one_pow, one_smul] at hrem
  have herr := hreverse.trans hrem
  rw [htransport, hinit, hend] at herr
  have hpoint : γ 1 = e v := by simp [γ]
  have hnormpoint : g.tangentNorm (γ 1) (mfderiv (𝓡 n) (𝓡 n) e v w) =
      g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w) :=
    congrArg (fun x : M => g.tangentNorm x
      (show EuclideanSpace ℝ (Fin n) from mfderiv (𝓡 n) (𝓡 n) e v w)) hpoint
  rw [hnormpoint] at herr
  exact herr


theorem radial_geodesic_metric_error
    (g : RiemannianMetric n M) (D : LeviCivitaData g)
    {e : EuclideanSpace ℝ (Fin n) → M} {R K : ℝ}
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v))
        {t : ℝ | t • v ∈ Metric.ball 0 R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R)
    (hK : ∀ t ∈ Icc (0 : ℝ) 1, D.curvatureTensorNorm (e (t • v)) ≤ K)
    (hc : ∀ t ∈ Icc (0 : ℝ) 1,
      g.tangentNorm (e (t • v))
        (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖)
    (w : EuclideanSpace ℝ (Fin n)) :
    let δ := (K * ‖v‖ ^ 2) * Real.exp (max 1 (K * ‖v‖ ^ 2)) / 6
    |g.pullbackCoefficients e v w w - ‖w‖ ^ 2| ≤ δ * (2 + δ) * ‖w‖ ^ 2 := by
  let δ := (K * ‖v‖ ^ 2) * Real.exp (max 1 (K * ‖v‖ ^ 2)) / 6
  let N := g.tangentNorm (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans (hK 0 (by simp))
  have hδ : 0 ≤ δ := by dsimp [δ]; positivity
  have hN : 0 ≤ N := Real.sqrt_nonneg _
  have herr : |N - ‖w‖| ≤ δ * ‖w‖ :=
    g.radial_geodesic_differential_norm_error D he hnorm hgeo hv hK hc w
  have hsum : N + ‖w‖ ≤ (2 + δ) * ‖w‖ := by
    have hh := (abs_le.mp herr).2
    nlinarith only [hh]
  have hpos : 0 ≤ g.pullbackCoefficients e v w w := by
    change 0 ≤ g.inner (e v) (mfderiv (𝓡 n) (𝓡 n) e v w)
      (mfderiv (𝓡 n) (𝓡 n) e v w)
    by_cases hz : mfderiv (𝓡 n) (𝓡 n) e v w = 0
    · simp [hz]
    · exact (g.pos _ _ hz).le
  have hsquare : g.pullbackCoefficients e v w w = N ^ 2 :=
    (Real.sq_sqrt hpos).symm
  change _ ≤ δ * (2 + δ) * ‖w‖ ^ 2
  rw [hsquare, show N ^ 2 - ‖w‖ ^ 2 = (N - ‖w‖) * (N + ‖w‖) by ring,
    abs_mul, abs_of_nonneg (add_nonneg hN (norm_nonneg w))]
  calc
    _ ≤ (δ * ‖w‖) * ((2 + δ) * ‖w‖) :=
      mul_le_mul herr hsum (add_nonneg hN (norm_nonneg w)) (by positivity)
    _ = _ := by ring


theorem exists_uniform_nearEuclidean_radial_radius {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε) (K : ℝ) :
    ∃ ρ : ℝ, 0 < ρ ∧ 2 * ρ < R ∧ ∀ s : ℝ, |s| ≤ 2 * ρ →
      let δ := (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) / 6
      δ * (2 + δ) ≤ ε := by
  let f : ℝ → ℝ := fun s =>
    let δ := (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) / 6
    δ * (2 + δ)
  have hf : ContinuousAt f 0 := by dsimp [f]; fun_prop
  have hnear := hf.eventually_lt continuousAt_const (by simpa [f] using hε)
  obtain ⟨η, hη, hsmall⟩ := Metric.eventually_nhds_iff.mp hnear
  refine ⟨min (R / 4) (η / 4), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · have hh := min_le_left (R / 4) (η / 4)
    linarith
  · intro s hs
    apply (hsmall (y := s) ?_).le
    rw [Real.dist_eq, sub_zero]
    have hh := min_le_right (R / 4) (η / 4)
    linarith


theorem radial_exponential_nearEuclidean
    (g : RiemannianMetric n M) (D : LeviCivitaData g) {p : M}
    {e : EuclideanSpace ℝ (Fin n) → M} {R K ρ ε : ℝ}
    (hρR : 2 * ρ < R)
    (hsmall : ∀ s : ℝ, |s| ≤ 2 * ρ →
      let δ := (K * s ^ 2) * Real.exp (max 1 (K * s ^ 2)) / 6
      δ * (2 + δ) ≤ ε)
    (he : ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R))
    (hnorm : ∀ u w, g.pullbackCoefficients e 0 u w = inner ℝ u w)
    (hgeo : ∀ v ∈ Metric.ball 0 R,
      g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
      ∀ t ∈ Icc (0 : ℝ) 1,
        g.tangentNorm (e (t • v))
          (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun s : ℝ => e (s • v)) t 1) = ‖v‖ ∧
        g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t)
    (hK : ∀ x ∈ g.ball p R, D.curvatureTensorNorm x ≤ K) :
    ∀ v ∈ Metric.closedBall 0 (2 * ρ), ∀ w,
      |g.pullbackCoefficients e v w w - ‖w‖ ^ 2| ≤ ε * ‖w‖ ^ 2 := by
  intro v hv w
  have hvn : ‖v‖ ≤ 2 * ρ := by simpa only [Metric.mem_closedBall, dist_zero_right] using hv
  have hvR : v ∈ Metric.ball 0 R := by
    simpa only [Metric.mem_ball, dist_zero_right] using hvn.trans_lt hρR
  have herr := g.radial_geodesic_metric_error D he hnorm (fun u hu => (hgeo u hu).1)
    hvR (fun t ht => hK _ (g.radial_image_mem_ball hvR ht ((hgeo v hvR).2 t ht).2))
    (fun t ht => ((hgeo v hvR).2 t ht).1) w
  exact herr.trans (mul_le_mul_of_nonneg_right
    (hsmall ‖v‖ (by simpa only [abs_of_nonneg (norm_nonneg v)] using hvn)) (sq_nonneg _))

end PoincareConjecture.RiemannianMetric
