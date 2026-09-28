import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Distance.BallCoverage

set_option autoImplicit false

open Set
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_minimizing_velocity_for_exponential
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v, g.tangentNorm p v < R →
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v)
    {q : M} (hq : q ∈ g.ball p R) :
    ∃ v : EuclideanSpace ℝ (Fin n), g.tangentNorm p v < R ∧
      e v = q ∧ ENNReal.ofReal (g.tangentNorm p v) = g.edist p q := by
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_precompact_ball p q hR hcompact hq
  have hzero : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by constructor <;> linarith
  let v := deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0
  have hγv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 :=
    (hγ.hasDerivAt_chart_at hzero p
      (by simpa only [hγ0] using mem_extChartAt_source p)).1
  have hnorm : ENNReal.ofReal (g.tangentNorm p v) = g.edist p q :=
    hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hγv hmin
  have hv : g.tangentNorm p v < R := by
    apply (ENNReal.ofReal_lt_ofReal_iff hR).mp
    rw [hnorm]
    exact hq
  obtain ⟨δ, hδ, η, hη, hη0, hηv, hη1⟩ := hexp v hv
  have hγ' : g.IsGeodesicOn γ (Icc (0 : ℝ) 1) :=
    fun s hs => hγ s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hη' : g.IsGeodesicOn η (Icc (0 : ℝ) 1) :=
    fun s hs => hη s ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hend := geodesic_endpoint_eq_of_initial_data hγ' hη' hγ0 hη0 hγv hηv
  exact ⟨v, hv, hη1.symm.trans (hend.symm.trans hγ1), hnorm⟩

theorem exponential_image_tangent_ball_eq
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v, g.tangentNorm p v < R →
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v)
    (hbound : ∀ v, g.tangentNorm p v < R →
      g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v))
    {r : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    e '' {v | g.tangentNorm p v < r} = g.ball p r := by
  apply Subset.antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact lt_of_le_of_lt (hbound v (hv.trans_le hrR))
      ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hv)
  · intro q hq
    have hqR : q ∈ g.ball p R := hq.trans_le (ENNReal.ofReal_le_ofReal hrR)
    obtain ⟨v, _, hev, hnorm⟩ :=
      g.exists_minimizing_velocity_for_exponential p hR hcompact e hexp hqR
    refine ⟨v, ?_, hev⟩
    apply (ENNReal.ofReal_lt_ofReal_iff hr).mp
    rw [hnorm]
    exact hq

theorem exponential_radial_edist_of_injective
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R)))
    (e : EuclideanSpace ℝ (Fin n) → M)
    (hexp : ∀ v, g.tangentNorm p v < R →
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v)
    (hbound : ∀ v, g.tangentNorm p v < R →
      g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v))
    (hinj : InjOn e {v | g.tangentNorm p v < R})
    {v : EuclideanSpace ℝ (Fin n)} (hv : g.tangentNorm p v < R) :
    g.edist p (e v) = ENNReal.ofReal (g.tangentNorm p v) := by
  have hmem : e v ∈ g.ball p R := (hbound v hv).trans_lt
    ((ENNReal.ofReal_lt_ofReal_iff hR).mpr hv)
  obtain ⟨w, hw, hew, hnorm⟩ :=
    g.exists_minimizing_velocity_for_exponential p hR hcompact e hexp hmem
  exact hnorm.symm.trans (congrArg (fun z => ENNReal.ofReal (g.tangentNorm p z))
    (hinj hw hv hew))

theorem exists_smooth_exponential_with_ball_images
    (g : RiemannianMetric n M) (p : M) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (closure (g.ball p R))) :
    ∃ e : EuclideanSpace ℝ (Fin n) → M,
      ContMDiffOn (𝓡 n) (𝓡 n) ∞ e {v | g.tangentNorm p v < R} ∧
      e 0 = p ∧
      HasFDerivAt (fun v => extChartAt (𝓡 n) p (e v))
        (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin n))) 0 ∧
      (∀ v, g.tangentNorm p v < R →
        ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
          g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
          HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v) ∧
      (∀ v, g.tangentNorm p v < R →
        g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v)) ∧
      ∀ r : ℝ, 0 < r → r ≤ R →
        e '' {v | g.tangentNorm p v < r} = g.ball p r := by
  have hnorm (v : EuclideanSpace ℝ (Fin n)) :
      Real.sqrt (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm
        (extChartAt (𝓡 n) p p) v v) = g.tangentNorm p v := by
    unfold tangentNorm
    rw [g.chartCoefficients_self]
  obtain ⟨e, he, he0, hderiv, hgeo⟩ :=
    g.exists_exponential_of_precompact_ball p hR hcompact
  simp only [hnorm] at he hgeo
  have hexp v (hv : g.tangentNorm p v < R) :
      ∃ ε : ℝ, 0 < ε ∧ ∃ γ : ℝ → M,
        g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 ∧ γ 1 = e v := by
    obtain ⟨ε, hε, γ, hγ, hγ0, hγv, hγ1, _⟩ := hgeo v hv
    exact ⟨ε, hε, γ, hγ, hγ0, hγv, hγ1⟩
  have hbound v (hv : g.tangentNorm p v < R) :
      g.edist p (e v) ≤ ENNReal.ofReal (g.tangentNorm p v) := by
    obtain ⟨_, _, _, _, _, _, _, hb⟩ := hgeo v hv
    exact hb
  exact ⟨e, he, he0, hderiv, hexp, hbound,
    fun _ hr hrR => g.exponential_image_tangent_ball_eq p hR hcompact e hexp hbound hr hrR⟩

end PoincareConjecture.RiemannianMetric
