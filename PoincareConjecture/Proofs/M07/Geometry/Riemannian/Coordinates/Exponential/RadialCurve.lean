import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Orthonormal
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.Exponential.Scaling

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M}

theorem IsGeodesicOn.comp_mul {γ : ℝ → M} {s : Set ℝ}
    (hγ : g.IsGeodesicOn γ s) (a : ℝ) :
    g.IsGeodesicOn (fun t => γ (a * t)) ((fun t => a * t) ⁻¹' s) := by
  intro t ht
  obtain ⟨p, q, w, hlocal⟩ := hγ (a * t) ht
  refine ⟨p, fun u => q (a * u), fun u => a • w (a * u), ?_⟩
  have hcont : ContinuousAt (fun u : ℝ => a * u) t := by fun_prop
  filter_upwards [hcont.preimage_mem_nhds hlocal] with u hu
  have hphase := hu.2.2.1.prodMk hu.2.2.2
  have hd := CoordinateExponential.hasDerivAt_velocityScale
    (B := g.pullbackCoefficients (extChartAt (𝓡 n) p).symm)
    (c := a) (t := u) hphase
  exact ⟨hu.1, hu.2.1, hd.fst, hd.snd⟩

theorem exponential_eq_geodesic_of_initial_data [T2Space M]
    (p : M) {R : ℝ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v ∈ Metric.ball 0 R, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (L v) 0 ∧ γ 1 = e v)
    {v : EuclideanSpace ℝ (Fin n)}
    {ε : ℝ} (hε : 0 < ε) {γ : ℝ → M}
    (hγ : g.IsGeodesicOn γ (Ioo (-ε) (1 + ε))) (hp : γ 0 = p)
    (hd : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (L v) 0)
    {t : ℝ} (ht : t ∈ Ioo (-ε) (1 + ε))
    (htv : t • v ∈ Metric.ball 0 R) : e (t • v) = γ t := by
  obtain ⟨δ, hδ, η, hη, hη0, hηd, hη1⟩ := hexp (t • v) htv
  have hscale : g.IsGeodesicOn (fun u => γ (t * u)) (Icc (0 : ℝ) 1) := by
    intro u hu
    apply hγ.comp_mul t u
    change t * u ∈ Ioo (-ε) (1 + ε)
    simpa only [smul_eq_mul, mul_comm] using
      (convex_Ioo (-ε) (1 + ε)).smul_mem_of_zero_mem
        (by constructor <;> linarith) ht hu
  have hη' : g.IsGeodesicOn η (Icc (0 : ℝ) 1) := by
    intro u hu
    exact hη u ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hd' : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ (t * u)))
      (t • L v) 0 := by
    have hdc : HasDerivAt (fun u => extChartAt (𝓡 n) p (γ u)) (L v) (t * 0) := by
      simpa only [mul_zero] using hd
    simpa only [mul_one, Function.comp_def] using
      hdc.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul t)
  have heq := hscale.eq_nhds_on_of_initial_data hη' (convex_Icc _ _).isPreconnected
    (t₀ := 0) (by simp) p (by simpa only [mul_zero, hp] using mem_extChartAt_source p)
    (by simpa only [mul_zero, hp] using hη0.symm)
    (by rw [hd'.deriv, hηd.deriv, map_smul])
  simpa only [mul_one, hη1] using (heq 1 (by simp)).self_of_nhds.symm

theorem isGeodesicOn_radial_of_initial_data [T2Space M]
    (p : M) {R : ℝ}
    (L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v ∈ Metric.ball 0 R, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (L v) 0 ∧ γ 1 = e v)
    {v : EuclideanSpace ℝ (Fin n)} (hv : v ∈ Metric.ball 0 R) :
    g.IsGeodesicOn (fun t : ℝ => e (t • v)) {t : ℝ | t • v ∈ Metric.ball 0 R} := by
  intro t ht
  have hc : ContinuousAt (fun u : ℝ => u • v) t := by fun_prop
  have hdomain : ∀ᶠ u in 𝓝 t, u • v ∈ Metric.ball 0 R :=
    hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds ht)
  by_cases ht0 : t = 0
  · subst t
    obtain ⟨ε, hε, γ, hγ, hp, hd, _⟩ := hexp v hv
    have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    obtain ⟨q, x, w, hlocal⟩ := hγ 0 h0
    refine ⟨q, x, w, ?_⟩
    filter_upwards [hlocal, hdomain, isOpen_Ioo.mem_nhds h0] with u hu huv huI
    exact ⟨(exponential_eq_geodesic_of_initial_data p L e hexp hε hγ hp hd huI huv).trans
      hu.1, hu.2⟩
  · obtain ⟨ε, hε, γ, hγ, hp, hd, _⟩ := hexp (t • v) ht
    have h1 : (1 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
    have htime : t⁻¹ * t ∈ Ioo (-ε) (1 + ε) := by simpa [ht0] using h1
    obtain ⟨q, x, w, hlocal⟩ := hγ.comp_mul t⁻¹ t htime
    have hc' : ContinuousAt (fun u : ℝ => t⁻¹ * u) t := by fun_prop
    have hnear := hc'.preimage_mem_nhds (isOpen_Ioo.mem_nhds htime)
    refine ⟨q, x, w, ?_⟩
    filter_upwards [hlocal, hdomain, hnear] with u hu huv huI
    have hscale : (t⁻¹ * u) • (t • v) = u • v := by
      rw [smul_smul, mul_right_comm, inv_mul_cancel₀ ht0, one_mul]
    have heq := exponential_eq_geodesic_of_initial_data p L e hexp hε hγ hp hd huI
      (by simpa only [hscale] using huv)
    rw [hscale] at heq
    exact ⟨heq.trans hu.1, hu.2⟩

theorem exists_orthonormal_radial_exponential_of_precompact_ball [T2Space M]
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    let E := EuclideanSpace ℝ (Fin n)
    let c := extChartAt (𝓡 n) p
    ∃ L : E ≃L[ℝ] E, ∃ e : E → M,
      (∀ v w, g.pullbackCoefficients c.symm (c p) (L v) (L w) = inner ℝ v w) ∧
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e (Metric.ball 0 R) ∧ e 0 = p ∧
      HasFDerivAt (fun v => c (e v)) L.toContinuousLinearMap 0 ∧
      ∀ v ∈ Metric.ball 0 R,
        g.IsGeodesicOn (fun t : ℝ => e (t • v))
          {t : ℝ | t • v ∈ Metric.ball 0 R} ∧
        ∀ t ∈ Icc (0 : ℝ) 1,
          g.tangentNorm (e (t • v))
            (mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t 1) = ‖v‖ ∧
          g.edist p (e (t • v)) ≤ ENNReal.ofReal ‖v‖ * ENNReal.ofReal t := by
  dsimp only
  obtain ⟨L, e, hL, he, he0, hed, hgeo⟩ :=
    g.exists_orthonormal_exponential_of_precompact_ball p hR hcompact
  have hexp : ∀ v ∈ Metric.ball 0 R, ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
      g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (L v) 0 ∧ γ 1 = e v := by
    intro v hv
    obtain ⟨ε, hε, γ, hγ, hp, hd, hend, _⟩ := hgeo v hv
    exact ⟨ε, hε, γ, hγ, hp, hd, hend⟩
  refine ⟨L, e, hL, he, he0, hed, ?_⟩
  intro v hv
  obtain ⟨ε, hε, γ, hγ, hp, hd, _, hspeed, hdist⟩ := hgeo v hv
  have htime {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t ∈ Ioo (-ε) (1 + ε) := by
    constructor <;> linarith [ht.1, ht.2]
  have hmem {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : t • v ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right] at hv ⊢
    rw [norm_smul, Real.norm_of_nonneg ht.1]
    exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg v)).trans_lt (by simpa using hv)
  have hgerm {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      (fun u : ℝ => e (u • v)) =ᶠ[𝓝 t] γ := by
    have hc : ContinuousAt (fun u : ℝ => u • v) t := by fun_prop
    filter_upwards [isOpen_Ioo.mem_nhds (htime ht),
      hc.preimage_mem_nhds (Metric.isOpen_ball.mem_nhds (hmem ht))] with u hu huv
    exact exponential_eq_geodesic_of_initial_data p L e hexp hε hγ hp hd hu huv
  constructor
  · exact isGeodesicOn_radial_of_initial_data p L e hexp hv
  · intro t ht
    have hgeq := hgerm ht
    have hpoint : e (t • v) = γ t := hgeq.self_of_nhds
    constructor
    · have hdEq := hgeq.mfderiv_eq (I := 𝓘(ℝ, ℝ)) (I' := 𝓡 n)
      change g.tangentNorm (e (t • v))
        ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t)
          (1 : ℝ)) = ‖v‖
      unfold tangentNorm
      change Real.sqrt (g.inner (e (t • v))
        ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t) (1 : ℝ))
        ((mfderiv (𝓘(ℝ, ℝ)) (𝓡 n) (fun u : ℝ => e (u • v)) t) (1 : ℝ))) = ‖v‖
      simp only [TangentSpace] at hdEq ⊢
      rw [hdEq, hpoint]
      exact hspeed t (htime ht)
    · rw [hpoint]
      simpa only [abs_of_nonneg ht.1] using hdist t (htime ht)

end PoincareConjecture.RiemannianMetric
