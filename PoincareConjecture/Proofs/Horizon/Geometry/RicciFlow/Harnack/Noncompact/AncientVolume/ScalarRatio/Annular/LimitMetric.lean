import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.AncientVolume.ScalarRatio.Annular.Compactness
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Metric.LocalExtension
import PoincareConjecture.Proofs.Horizon.Analysis.Calculus.SmoothCompactness.LocalConvergence













set_option autoImplicit false
set_option maxSynthPendingDepth 8
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.RiemannianMetric




theorem exists_local_metric_of_normalized_pullback_limit
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {U : Set (EuclideanSpace ℝ (Fin n))} (hU : IsOpen U) (hzero : 0 ∈ U)
    (g : ℕ → RiemannianMetric n M)
    (Φ : ℕ → EuclideanSpace ℝ (Fin n) → M)
    (B : EuclideanSpace ℝ (Fin n) →
      EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
    (hB : ContDiffOn ℝ ∞ B U)
    (hconv : ∀ x ∈ U, Tendsto (fun k => (g k).pullbackCoefficients (Φ k) x)
      atTop (𝓝 (B x)))
    (hnorm : ∀ v w, B 0 v w = inner ℝ v w) :
    ∃ (gLimit : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
      (_D : LeviCivitaData gLimit) (V : Set (EuclideanSpace ℝ (Fin n))),
      IsOpen V ∧ 0 ∈ V ∧ V ⊆ U ∧
        ∀ x ∈ V, gLimit.euclideanCoefficients x = B x := by
  have hsymm : ∀ x ∈ U, ∀ v w, B x v w = B x w v := by
    intro x hx v w
    have heval (v w : EuclideanSpace ℝ (Fin n)) :=
      ((ContinuousLinearMap.apply ℝ ℝ w).continuous.tendsto (B x v)).comp
        (((ContinuousLinearMap.apply ℝ
          (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) v).continuous.tendsto (B x)).comp (hconv x hx))
    exact tendsto_nhds_unique (heval v w)
      ((heval w v).congr (fun k => (g k).symm (Φ k x) _ _))
  have hclose : ∀ᶠ x in 𝓝 (0 : EuclideanSpace ℝ (Fin n)), ‖B x - B 0‖ < 1 / 2 := by
    have h := ((hB.contDiffAt (hU.mem_nhds hzero)).continuousAt.sub
      (continuousAt_const (y := B 0))).norm
    exact h.eventually (Iio_mem_nhds (by simp))
  obtain ⟨W, hW, hWo, hzeroW⟩ := mem_nhds_iff.mp (inter_mem (hU.mem_nhds hzero) hclose)
  have hWU : W ⊆ U := fun x hx => (hW hx).1
  have hpos : ∀ x ∈ W, ∀ v : EuclideanSpace ℝ (Fin n), v ≠ 0 → 0 < B x v v := by
    intro x hx v hv
    have hbound := ((B x - B 0) v).le_opNorm v
    have hbound' := (B x - B 0).le_opNorm v
    have habs : |B x v v - ‖v‖ ^ 2| ≤ ‖B x - B 0‖ * ‖v‖ ^ 2 := by
      have h := hbound.trans (mul_le_mul_of_nonneg_right hbound' (norm_nonneg v))
      simpa only [sub_apply, hnorm, real_inner_self_eq_norm_sq,
        Real.norm_eq_abs, mul_assoc, ← sq] using h
    have hsq : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    have hsmall := mul_lt_mul_of_pos_right (hW hx).2 hsq
    have hlow := (abs_le.mp habs).1
    nlinarith
  obtain ⟨gLimit, D, V, hVo, hzeroV, hVW, heq⟩ :=
    exists_local_realization hWo hzeroW B (hB.mono hWU)
      (fun x hx => hsymm x (hWU hx)) hpos
  exact ⟨gLimit, D, V, hVo, hzeroV, hVW.trans hWU, heq⟩

end PoincareConjecture.RiemannianMetric

namespace PoincareConjecture.RicciFlow




theorem exists_terminal_exponential_metric_subsequence
    {n : ℕ} {M : Type u} [TopologicalSpace M] [T3Space M]
    [SecondCountableTopology M] [ConnectedSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (hC : RicciFlowCurvatureTheory.{u}) {K S ρ : ℝ}
    (hK : 0 < K) (hS : 0 < S) (hρ : 0 < ρ) (hρS : ρ < S / 2)
    (F : ℕ → RicciFlow n M (Iic 0))
    (hcomplete : ∀ k t, t ≤ 0 → MetricComplete ((F k).metric t))
    (hoperator : ∀ k t, t ≤ 0 → ∀ x,
      ((F k).connection t).NonnegativeCurvatureOperator x)
    (p : ℕ → M)
    (hcurv : ∀ k t, t ≤ 0 → ∀ x ∈ ((F k).metric 0).ball (p k) (2 * S),
      ((F k).connection t).curvatureTensorNorm x ≤ K)
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
      ∃ (gLimit : RiemannianMetric n (EuclideanSpace ℝ (Fin n)))
        (_D : LeviCivitaData gLimit) (V : Set (EuclideanSpace ℝ (Fin n))),
        IsOpen V ∧ 0 ∈ V ∧ V ⊆ Metric.ball 0 ρ ∧
        (∀ v w, gLimit.inner 0 v w = inner ℝ v w) ∧
        (∀ m C, IsCompact C → C ⊆ V → TendstoUniformlyOn
          (fun k => iteratedFDeriv ℝ m
            (((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k))))
          (iteratedFDeriv ℝ m gLimit.euclideanCoefficients) atTop C) := by
  obtain ⟨σ, hσ, B, hB, hjets, hnorm⟩ :=
    exists_terminal_exponential_coefficient_subsequence hC hK hS hρ hρS F hcomplete
      hoperator p hcurv L Φ hsource hzero hL hderiv hgeo hdist
  have hzeroρ : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.ball 0 ρ :=
    Metric.mem_ball_self hρ
  have hconv : ∀ x ∈ Metric.ball 0 ρ, Tendsto
      (fun k => ((F (σ k)).metric 0).pullbackCoefficients (Φ (σ k)) x)
      atTop (𝓝 (B x)) := by
    intro x hx
    have hjet := hjets 0 {x} isCompact_singleton (singleton_subset_iff.mpr hx)
    have hvalue := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin n))).comp_tendstoUniformlyOn hjet
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using
      hvalue.tendsto_at (mem_singleton x)
  obtain ⟨gLimit, D, V, hVo, hzeroV, hVρ, heq⟩ :=
    RiemannianMetric.exists_local_metric_of_normalized_pullback_limit
      Metric.isOpen_ball hzeroρ (fun k => (F (σ k)).metric 0)
      (fun k => Φ (σ k)) B hB hconv hnorm
  refine ⟨σ, hσ, gLimit, D, V, hVo, hzeroV, hVρ, ?_, ?_⟩
  · intro v w
    exact (congrArg (fun A => A v w) (heq 0 hzeroV)).trans (hnorm v w)
  · intro m C hCcompact hCV
    exact (hjets m C hCcompact (hCV.trans hVρ)).congr_right
      ((Poincare.Analysis.Calculus.eqOn_iteratedFDeriv_of_isOpen hVo
        (fun x hx => (heq x hx).symm) m).mono hCV)

end PoincareConjecture.RicciFlow
