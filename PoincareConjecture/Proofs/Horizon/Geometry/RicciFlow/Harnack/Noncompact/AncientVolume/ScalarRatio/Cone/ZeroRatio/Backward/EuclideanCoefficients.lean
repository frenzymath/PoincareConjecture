import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Coordinates.Harmonic.NearEuclidean










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1000000

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.RicciFlow



theorem exists_terminal_exponential_euclidean_coefficient_subsequence
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    [T3Space M] [SecondCountableTopology M] [ConnectedSpace M]
    (hC : RicciFlowCurvatureTheory.{u}) {K S ρ : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S / 2)
    (F : ℕ → RicciFlow n M (Iic 0))
    (hcomplete : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hoperator : ∀ k t, t ≤ 0 → ∀ x,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (p : ℕ → M)
    (hcurv : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
      ((F k).connection t).curvatureTensorNorm x ≤ K)
    (hdecay : ∀ ε > 0, ∀ᶠ k in atTop,
      ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
        ((F k).connection 0).curvatureTensorNorm x ≤ ε)
    (L : ℕ → EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (Φ : ℕ → PartialDiffeomorph (𝓡 n) (𝓡 n) (EuclideanSpace ℝ (Fin n)) M ∞)
    (hsource : ∀ k, (Φ k).source = Metric.ball 0 S)
    (hzero : ∀ k, Φ k 0 = p k)
    (hL : ∀ k v w, ((F k).metric 0).pullbackCoefficients
      (extChartAt (𝓡 n) (p k)).symm (extChartAt (𝓡 n) (p k) (p k))
        (L k v) (L k w) = inner ℝ v w)
    (hderiv : ∀ k, HasFDerivAt (fun w => extChartAt (𝓡 n) (p k) (Φ k w))
      (L k).toContinuousLinearMap 0)
    (hgeo : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).IsGeodesicOn (fun t => Φ k (t • w))
        {t : ℝ | t • w ∈ Metric.ball 0 S})
    (hdist : ∀ k w, w ∈ Metric.ball 0 S →
      ((F k).metric 0).edist (p k) (Φ k w) = ENNReal.ofReal ‖w‖) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∀ m C, IsCompact C → C ⊆ Metric.ball 0 ρ → TendstoUniformlyOn
        (fun k => iteratedFDeriv ℝ m
          (((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k))))
        (iteratedFDeriv ℝ m (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ)) atTop C := by
  obtain ⟨σ, hσ, B, _, hjets, _⟩ :=
    exists_terminal_exponential_coefficient_subsequence hC hK hS hρ hρS F
      hcomplete hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
  have he (k : ℕ) : ContMDiffOn (𝓡 n) (𝓡 n) ∞ (Φ k) (Metric.ball 0 S) := by
    simpa only [hsource k] using (Φ k).contMDiffOn
  have hnorm (k : ℕ) (v w : EuclideanSpace ℝ (Fin n)) :
      ((F k).metric 0).pullbackCoefficients (Φ k) 0 v w = inner ℝ v w :=
    ((F k).metric 0).pullbackCoefficients_zero_of_orthonormal (p k)
      ((he k).contMDiffAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hS)))
      (hzero k) (hderiv k) (hL k) v w
  have hvalue (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ Metric.ball 0 ρ)
      (v w : EuclideanSpace ℝ (Fin n)) :
      Tendsto (fun k => ((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k)) x v w)
        atTop (𝓝 (B x v w)) := by
    have hjet := hjets 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    have hz := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    have hconv : Tendsto
        (fun k => ((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k)) x)
        atTop (𝓝 (B x)) := by
      simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
        hz.tendsto_at (mem_singleton x)
    exact ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B x v)).comp
      (((ContinuousLinearMap.apply ℝ
        (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto (B x)).comp hconv)
  have hB : EqOn B (fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ) (Metric.ball 0 ρ) := by
    intro x hx
    have hxn : ‖x‖ < S := by
      have hh : ‖x‖ < ρ := by simpa only [Metric.mem_ball, dist_zero_right] using hx
      linarith
    have hxS : x ∈ Metric.ball (0 : EuclideanSpace ℝ (Fin n)) S := by
      simpa only [Metric.mem_ball, dist_zero_right] using hxn
    have htx (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : t • x ∈ Metric.ball 0 S := by
      rw [Metric.mem_ball, dist_zero_right, norm_smul, Real.norm_of_nonneg ht.1]
      exact (mul_le_mul_of_nonneg_right ht.2 (norm_nonneg x)).trans_lt
        (by simpa only [one_mul] using hxn)
    have hdiag (w : EuclideanSpace ℝ (Fin n)) : B x w w = inner ℝ w w := by
      let err : ℝ → ℝ := fun ε =>
        let δ := (ε * ‖x‖ ^ 2) * Real.exp (max 1 (ε * ‖x‖ ^ 2)) / 6
        δ * (2 + δ) * ‖w‖ ^ 2
      have hbound (ε : ℝ) (hε : 0 < ε) : |B x w w - ‖w‖ ^ 2| ≤ err ε := by
        apply le_of_tendsto ((hvalue x hx w w).sub tendsto_const_nhds).abs
        filter_upwards [hσ.tendsto_atTop.eventually (hdecay ε hε)] with k hk
        exact ((F (σ k)).metric 0).radial_geodesic_metric_error
          ((F (σ k)).connection 0) (he (σ k)) (hnorm (σ k)) (hgeo (σ k)) hxS
          (fun t ht => hk _ (by
            change ((F (σ k)).metric 0).edist (p (σ k)) (Φ (σ k) (t • x)) <
              ENNReal.ofReal (2 * S)
            rw [hdist (σ k) (t • x) (htx t ht),
              ENNReal.ofReal_lt_ofReal_iff_of_nonneg (norm_nonneg _)]
            have htn : ‖t • x‖ < S := by
              simpa only [Metric.mem_ball, dist_zero_right] using htx t ht
            linarith))
          (fun t ht => ((F (σ k)).metric 0).tangentNorm_radial_of_normalized_exponential
            (p (σ k)) (L (σ k)) (hzero (σ k)) (hL (σ k))
            (hderiv (σ k)) (hgeo (σ k)) hxS ht) w
      have hecont : Continuous err := by dsimp [err]; fun_prop
      have helim : Tendsto (fun j : ℕ => err (1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        simpa only [err, zero_mul, zero_div, add_zero, mul_zero, Function.comp_def] using
          hecont.continuousAt.tendsto.comp (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      have hz : |B x w w - ‖w‖ ^ 2| ≤ 0 :=
        ge_of_tendsto helim (Eventually.of_forall fun j => hbound _ (by positivity))
      rw [real_inner_self_eq_norm_sq]
      exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hz (abs_nonneg _)))
    have hsym (v w : EuclideanSpace ℝ (Fin n)) : B x w v = B x v w := by
      apply tendsto_nhds_unique (hvalue x hx w v)
      apply (hvalue x hx v w).congr
      intro k
      exact ((F (σ k)).metric 0).symm (Φ (σ k) x) _ _
    ext v w
    have hp := hdiag (v + w)
    simp only [map_add, add_apply, inner_add_left, inner_add_right,
      hdiag, hsym, real_inner_comm w v] at hp
    rw [real_inner_comm v w] at hp
    change B x v w = inner ℝ v w
    linarith
  refine ⟨σ, hσ, ?_⟩
  intro m C hC hCρ
  apply (hjets m C hC hCρ).congr_right
  intro x hx
  have hnear : B =ᶠ[𝓝 x] fun _ : EuclideanSpace ℝ (Fin n) => innerSL ℝ :=
    Filter.mem_of_superset (Metric.isOpen_ball.mem_nhds (hCρ hx)) hB
  exact (hnear.iteratedFDeriv ℝ m).self_of_nhds

end PoincareConjecture.RicciFlow
