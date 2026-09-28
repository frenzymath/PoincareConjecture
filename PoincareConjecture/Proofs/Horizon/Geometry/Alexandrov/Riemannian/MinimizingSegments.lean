import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology ENNReal

namespace PoincareConjecture.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

private theorem segment_tangentNorm_smul (g : RiemannianMetric n M)
    (p : M) (v : EuclideanSpace ℝ (Fin n)) (c : ℝ) :
    g.tangentNorm p (c • v) = |c| * g.tangentNorm p v := by
  simp only [tangentNorm, map_smul, smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← pow_two, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem exists_unit_speed_minimizing_geodesic_of_metricComplete
    [T3Space M] [PreconnectedSpace M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p q : M)
    (hd : 0 < (g.edist p q).toReal) :
    ∃ γ : ℝ → M, γ 0 = p ∧ γ (g.edist p q).toReal = q ∧
      g.IsGeodesicOn γ (Icc (0 : ℝ) (g.edist p q).toReal) ∧
      (∀ t ∈ Icc (0 : ℝ) (g.edist p q).toReal,
        g.tangentNorm (γ t) (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) γ t 1) = 1) ∧
      (∀ s ∈ Icc (0 : ℝ) (g.edist p q).toReal,
        ∀ t ∈ Icc (0 : ℝ) (g.edist p q).toReal,
          g.edist (γ s) (γ t) = ENNReal.ofReal |s - t|) := by
  let d := (g.edist p q).toReal
  obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
    g.exists_minimizing_geodesic_of_metricComplete hc p q
  have h0 : (0 : ℝ) ∈ Ioo (-ε) (1 + ε) := by
    constructor <;> linarith
  let v := deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0
  have hv : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v 0 :=
    (hγ.hasDerivAt_chart_at h0 p
      (by simpa only [hγ0] using mem_extChartAt_source p)).1
  have hspeed : g.tangentNorm p v = d := by
    have h := hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hv hmin
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm p v from
      Real.sqrt_nonneg _)] using congrArg ENNReal.toReal h
  let η := fun t : ℝ => γ (t / d)
  have hη0 : η 0 = p := by simpa only [η, zero_div] using hγ0
  have hηgeo : g.IsGeodesicOn η (Ioo (-ε * d) ((1 + ε) * d)) := by
    intro t ht
    have htd : t / d ∈ Ioo (-ε) (1 + ε) :=
      ⟨(lt_div_iff₀ hd).2 ht.1, (div_lt_iff₀ hd).2 ht.2⟩
    have htd' : d⁻¹ * t ∈ Ioo (-ε) (1 + ε) := by
      simpa only [div_eq_mul_inv, mul_comm] using htd
    simpa only [η, div_eq_mul_inv, mul_comm] using hγ.comp_mul d⁻¹ t htd'
  have hI : Icc (0 : ℝ) d ⊆ Ioo (-ε * d) ((1 + ε) * d) := by
    intro t ht
    have hεδ : 0 < ε * d := mul_pos hε hd
    constructor <;> nlinarith [ht.1, ht.2]
  have hηv : HasDerivAt (fun t => extChartAt (𝓡 n) p (η t)) (d⁻¹ • v) 0 := by
    have hv' : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) v (d⁻¹ * 0) := by
      simpa only [mul_zero] using hv
    simpa only [η, Function.comp_def, mul_one, one_mul, div_eq_mul_inv, mul_comm] using
      hv'.scomp 0 ((hasDerivAt_id (0 : ℝ)).const_mul d⁻¹)
  have hηzero : (0 : ℝ) ∈ Ioo (-ε * d) ((1 + ε) * d) :=
    hI ⟨le_rfl, hd.le⟩
  obtain ⟨C, hC⟩ := hηgeo.exists_constant_tangentNorm
    (hηzero.1.trans hηzero.2)
  have hC0 : g.tangentNorm p (d⁻¹ • v) = C := by
    simpa only [chartCoefficients_self, tangentNorm] using
      (hηgeo.tangentNorm_initial hηzero hη0 hηv).symm.trans (hC 0 hηzero)
  have hCone : (C : ℝ) = 1 := by
    rw [← hC0, segment_tangentNorm_smul, abs_of_pos (inv_pos.mpr hd), hspeed,
      inv_mul_cancel₀ hd.ne']
  refine ⟨η, hη0, ?_, (fun t ht => hηgeo t (hI ht)), ?_, ?_⟩
  · change γ (d / d) = q
    rw [div_self (show d ≠ 0 from hd.ne')]
    exact hγ1
  · intro t ht
    exact (hC t (hI ht)).trans hCone
  · intro s hs t ht
    have hunit {u : ℝ} (hu : u ∈ Icc (0 : ℝ) d) : u / d ∈ Icc (0 : ℝ) 1 :=
      ⟨div_nonneg hu.1 hd.le, (div_le_one hd).mpr hu.2⟩
    have hdist : g.edist p q = ENNReal.ofReal d :=
      (ENNReal.ofReal_toReal (g.edist_ne_top p q)).symm
    change g.edist (γ (s / d)) (γ (t / d)) = _
    rw [hmin _ (hunit hs) _ (hunit ht), hdist,
      ← ENNReal.ofReal_mul (abs_nonneg _), ← sub_div, abs_div, abs_of_pos hd,
      div_mul_cancel₀ _ hd.ne']

end PoincareConjecture.RiemannianMetric
