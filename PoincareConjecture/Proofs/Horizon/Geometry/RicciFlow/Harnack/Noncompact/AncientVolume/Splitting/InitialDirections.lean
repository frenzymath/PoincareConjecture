import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Comparison.Laplacian.Branch.Complete
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Distance.SegmentSpeed
import Mathlib.Topology.MetricSpace.Sequences

















set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

namespace PoincareConjecture.RiemannianMetric



theorem exists_convergent_initial_directions_of_metricComplete
    {n : ℕ} {M : Type*} [TopologicalSpace M] [T3Space M] [PreconnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (g : RiemannianMetric n M) (hc : MetricComplete g) (p : M) (q : ℕ → M)
    (hescape : Tendsto (fun i => (g.edist p (q i)).toReal) atTop atTop) :
    letI : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
      ⟨g.toRiemannianMetric⟩
    ∃ s : ℕ → ℕ, StrictMono s ∧ ∃ ε : ℕ → ℝ, ∃ γ : ℕ → ℝ → M,
      ∃ v : ℕ → TangentSpace (𝓡 n) p, ∃ vlim : TangentSpace (𝓡 n) p,
      (∀ i, 0 < ε i ∧ g.IsGeodesicOn (γ i) (Ioo (-ε i) (1 + ε i)) ∧
        γ i 0 = p ∧ γ i 1 = q (s i) ∧
        (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
          g.edist (γ i a) (γ i b) = ENNReal.ofReal |a - b| * g.edist p (q (s i))) ∧
        HasDerivAt (fun t => extChartAt (𝓡 n) p (γ i t))
          ((g.edist p (q (s i))).toReal • v i) 0 ∧
        g.tangentNorm p (v i) = 1 ∧ 0 < (g.edist p (q (s i))).toReal) ∧
      Tendsto v atTop (𝓝 vlim) ∧ g.tangentNorm p vlim = 1 ∧
      Tendsto (fun i => (g.edist p (q (s i))).toReal) atTop atTop := by
  classical
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : FiniteDimensional ℝ (TangentSpace (𝓡 n) p) :=
    VectorBundle.finiteDimensional ℝ (EuclideanSpace ℝ (Fin n))
      (TangentSpace (𝓡 n) : M → Type _) p
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hescape.eventually_gt_atTop 0)
  let d : ℕ → ℝ := fun i => (g.edist p (q (N + i))).toReal
  have hd (i : ℕ) : 0 < d i := hN (N + i) (Nat.le_add_right N i)
  have hsegments (i : ℕ) : ∃ ε : ℝ, ∃ γ : ℝ → M, ∃ v : TangentSpace (𝓡 n) p,
      0 < ε ∧ g.IsGeodesicOn γ (Ioo (-ε) (1 + ε)) ∧ γ 0 = p ∧ γ 1 = q (N + i) ∧
      (∀ a ∈ Icc (0 : ℝ) 1, ∀ b ∈ Icc (0 : ℝ) 1,
        g.edist (γ a) (γ b) = ENNReal.ofReal |a - b| * g.edist p (q (N + i))) ∧
      HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) (d i • v) 0 ∧
      g.tangentNorm p v = 1 := by
    obtain ⟨ε, hε, γ, hγ, hγ0, hγ1, hmin⟩ :=
      g.exists_minimizing_geodesic_of_metricComplete hc p (q (N + i))
    let w : TangentSpace (𝓡 n) p := deriv (fun t => extChartAt (𝓡 n) p (γ t)) 0
    have hw : HasDerivAt (fun t => extChartAt (𝓡 n) p (γ t)) w 0 :=
      (hγ.hasDerivAt_chart_at (show (0 : ℝ) ∈ Ioo (-ε) (1 + ε) by
        constructor <;> linarith) p
        (by simpa only [hγ0] using mem_extChartAt_source p)).1
    have hspeed : g.tangentNorm p w = d i := by
      have h := congrArg ENNReal.toReal
        (hγ.initial_tangentNorm_eq_of_edist_segment hε hγ0 hw hmin)
      rw [ENNReal.toReal_ofReal (show 0 ≤ g.tangentNorm p w from Real.sqrt_nonneg _)] at h
      exact h
    let v : TangentSpace (𝓡 n) p := (d i)⁻¹ • w
    have hnormalized : d i • v = w := by
      simp only [v, smul_smul, mul_inv_cancel₀ (hd i).ne', one_smul]
    have hnorm : g.tangentNorm p v = 1 := by
      change ‖(d i)⁻¹ • w‖ = 1
      have hnormw : ‖w‖ = d i := hspeed
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (hd i)),
        hnormw, inv_mul_cancel₀ (hd i).ne']
    exact ⟨ε, γ, v, hε, hγ, hγ0, hγ1, hmin, by rwa [hnormalized], hnorm⟩
  choose ε γ v hε hγ hγ0 hγ1 hmin hderiv hnorm using hsegments
  obtain ⟨vlim, hvlim, σ, hσ, hvs⟩ :=
    (isCompact_sphere (0 : TangentSpace (𝓡 n) p) 1).tendsto_subseq
      (show ∀ i, v i ∈ Metric.sphere (0 : TangentSpace (𝓡 n) p) 1 by
        intro i
        rw [Metric.mem_sphere, dist_zero_right]
        exact hnorm i)
  let s : ℕ → ℕ := fun i => N + σ i
  have hs : StrictMono s := fun _ _ hij => Nat.add_lt_add_left (hσ hij) N
  refine ⟨s, hs, ε ∘ σ, γ ∘ σ, v ∘ σ, vlim, ?_, hvs, ?_, ?_⟩
  · intro i
    exact ⟨hε (σ i), hγ (σ i), hγ0 (σ i), hγ1 (σ i), hmin (σ i),
      hderiv (σ i), hnorm (σ i), hd (σ i)⟩
  · change ‖vlim‖ = 1
    simpa using hvlim
  · exact hescape.comp hs.tendsto_atTop

end PoincareConjecture.RiemannianMetric
