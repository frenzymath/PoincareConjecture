import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Compactness.TerminalDerivatives
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl.ScalarEvolution
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Harnack.Matrix.Bounds
import Mathlib.Analysis.Calculus.Deriv.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

private theorem scalar_time_bound_of_second_curvature_derivative
    (P : M23NormalizedKappaCompactnessPredecessors)
    {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
    (F : RicciFlow 3 M (Iic 0)) (p : M) {C : ℝ}
    (hderiv : ∀ s ≤ 0, (F.connection s).curvatureDerivativeNorm 2 p ≤ C)
    (hscalar : ∀ s ≤ 0, 0 ≤ (F.connection s).scalarCurvature p ∧
      (F.connection s).scalarCurvature p ≤ 1)
    (hoperator : ∀ s ≤ 0, (F.connection s).NonnegativeCurvatureOperator p)
    {t : ℝ} (ht : t ≤ 0) :
    (F.connection 0).scalarCurvature p - (F.connection t).scalarCurvature p ≤
      (3 ^ 3 * C + 2) * (0 - t) := by
  have hreg : ContinuousOn (fun s => (F.connection s).scalarCurvature p) (Icc t 0) :=
    (P.scalar_regular M (Iic 0) F).continuousOn.comp (f := fun s : ℝ => (s, p))
      (continuous_id.prodMk continuous_const).continuousOn (fun s hs => ⟨hs.2, mem_univ p⟩)
  have hevol (s : ℝ) (hs : s ∈ interior (Icc t 0)) :
      HasDerivAt (fun u => (F.connection u).scalarCurvature p)
        ((F.connection s).laplacian (F.connection s).scalarCurvature p +
          2 * (F.connection s).ricciNormSq p) s := by
    have hs0 : s < 0 := (show s ∈ Ioo t 0 from by simpa only [interior_Icc] using hs).2
    exact (P.scalar_evolution M (Iic 0) F s hs0.le p).hasDerivAt (Iic_mem_nhds hs0)
  have hslope (s : ℝ) (hs : s ∈ interior (Icc t 0)) :
      deriv (fun u => (F.connection u).scalarCurvature p) s ≤ 3 ^ 3 * C + 2 := by
    have hs0 : s ≤ 0 := (interior_subset hs).2
    have hcalc := P.tensor_calculus 3 M (F.metric s) (F.connection s)
    have hnonneg := (hscalar s hs0).1
    have hupper := (hscalar s hs0).2
    have hRic : ∀ v, 0 ≤ (F.connection s).ricci p v v := fun v =>
      ((F.connection s).ricci_bounds_of_nonnegative_curvatureOperator hcalc p
        (hoperator s hs0) v).1
    have hreaction := (F.connection s).ricciNormSq_le_scalarCurvature_sq_of_ricci_nonneg
      hcalc p hRic
    have hlap := ((F.connection s).abs_laplacian_scalar_le_curvatureDerivativeNorm
      hcalc p).trans (mul_le_mul_of_nonneg_left (hderiv s hs0) (by positivity))
    have hsq : (F.connection s).scalarCurvature p ^ 2 ≤ (1 : ℝ) ^ 2 :=
      pow_le_pow_left₀ hnonneg hupper 2
    rw [(hevol s hs).deriv]
    norm_num at hlap hsq ⊢
    nlinarith [le_abs_self ((F.connection s).laplacian (F.connection s).scalarCurvature p)]
  exact (convex_Icc t 0).image_sub_le_mul_sub_of_deriv_le hreg
    (fun s hs => (hevol s hs).differentiableAt.differentiableWithinAt)
    hslope t ⟨le_rfl, ht⟩ 0 ⟨ht, le_rfl⟩ ht

namespace NormalizedKappaSolutionSequence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.measurableSpace
  FlowCarrier.borelSpace FlowCarrier.chartedSpace FlowCarrier.isManifold
  FlowCarrier.t2Space FlowCarrier.t3Space FlowCarrier.secondCountable

variable {kappa : ℝ} (S : NormalizedKappaSolutionSequence kappa)

local instance scalarBufferSourceConnected (k : ℕ) : ConnectedSpace (S.term k).carrier.carrier :=
  (S.term k).connectedSpace

theorem exists_base_scalar_time_constant
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S) :
    ∃ D : ℝ, 0 < D ∧ ∀ k : ℕ, ∀ t : ℝ, t ≤ 0 →
      1 - ((S.term k).flow.flow.connection t).scalarCurvature (S.term k).base ≤
        D * (0 - t) := by
  obtain ⟨C, hC, hderiv⟩ := S.allTime_curvatureDerivativeNorm_le P hcontrol
    1 (by norm_num) 2
  refine ⟨3 ^ 3 * C + 2, by positivity, ?_⟩
  intro k t ht
  let B := S.term k
  let F := B.flow.flow
  let p := B.base
  have hp : p ∈ (F.metric 0).ball p 1 := by
    change (F.metric 0).edist p p < ENNReal.ofReal 1
    simp only [RiemannianMetric.edist, Manifold.riemannianEDist_self]
    positivity
  have hscalar (s : ℝ) (hs : s ≤ 0) :
      0 ≤ (F.connection s).scalarCurvature p ∧ (F.connection s).scalarCurvature p ≤ 1 := by
    refine ⟨(P.scalar_pos B.carrier.carrier B.flow s hs p).le, ?_⟩
    have h := P.scalar_monotone B.carrier.carrier B.flow s 0 hs le_rfl p
    rwa [B.scalar_normalized] at h
  have h := scalar_time_bound_of_second_curvature_derivative P F p
    (fun s hs => hderiv k s hs p hp) hscalar
    (fun s hs => B.flow.nonnegative_curvature_operator s hs p) ht
  simpa only [F, p, B.scalar_normalized] using h

theorem exists_base_scalar_positive_time_buffer
    (P : M23NormalizedKappaCompactnessPredecessors)
    (hcontrol : M23AllTimeCurvatureControl S) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ k : ℕ, ∀ t ∈ Icc (-δ) 0,
      (1 : ℝ) / 2 ≤ ((S.term k).flow.flow.connection t).scalarCurvature (S.term k).base := by
  obtain ⟨D, hD, htime⟩ := S.exists_base_scalar_time_constant P hcontrol
  let δ := min (1 / 2 : ℝ) (1 / (2 * D))
  have hδ : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδD : D * δ ≤ 1 / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * D)).mp
      (show δ ≤ 1 / (2 * D) from min_le_right _ _)
    nlinarith
  refine ⟨δ, hδ, by linarith, ?_⟩
  intro k t ht
  have h := htime k t ht.2
  have htime' : D * (0 - t) ≤ D * δ :=
    mul_le_mul_of_nonneg_left (by linarith [ht.1]) hD.le
  linarith

end NormalizedKappaSolutionSequence
end PoincareConjecture
