import PoincareConjecture.Proofs.M30.Thm5_6_PartialLimits.StaticStageMetricJets
import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Coordinates.CompactFamily
import PoincareConjecture.Proofs.M04.TensorNorm
import PoincareConjecture.Proofs.M28.Mathlib.WithinConvergenceBounds
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.BackwardMetricComparison
import PoincareConjecture.Proofs.M28.Thm5_6_PartialLimits.Geometry.Parabolic.MixedBounds










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M30.PartialPointedMetricConvergence

attribute [local instance] FlowCarrier.topologicalSpace FlowCarrier.chartedSpace
  FlowCarrier.isManifold

variable {M : ℕ → Type u} [∀ k, TopologicalSpace (M k)]
  [∀ k, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (M k)]
  [∀ k, IsManifold (𝓡 3) ∞ (M k)]
  {g : ∀ k, RiemannianMetric 3 (M k)} {p : ∀ k, M k} {A : ℝ}

set_option synthInstance.maxHeartbeats 200000 in

set_option maxHeartbeats 1800000 in





theorem exists_static_stage_coordinate_bounds
    (G : PartialPointedMetricConvergence g p A) (j N : ℕ)
    {tau : ℝ} (htau : 0 < tau) :
    let Y : TopologicalSpace.Opens G.limitCarrier.carrier :=
      ⟨G.exhaustion j, G.exhaustion_open j⟩
    ∀ P : ℕ → RicciFlow 3 Y (Icc (-tau) 0),
      (∀ (k : ℕ) (x : Y) (v w : TangentSpace (𝓡 3) x),
        ((P k).metric 0).inner x v w = (g (G.subsequence (k + N))).inner
          (G.embedding (k + N) x.val)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x v)
          (mfderiv (𝓡 3) (𝓡 3) (fun y : Y => G.embedding (k + N) y.val) x w)) →
      (∀ m : ℕ, ∃ D : ℝ, 0 ≤ D ∧ ∀ k t, t ∈ Icc (-tau) 0 → ∀ x : Y,
        ((P k).connection t).curvatureDerivativeNorm m x ≤ D) →
      ∀ (q : G.limitCarrier.carrier) (U : Set (EuclideanSpace ℝ (Fin 3))),
        IsOpen U → U ⊆ (extChartAt (𝓡 3) q).target →
        ∀ ψ : EuclideanSpace ℝ (Fin 3) → Y,
          ContMDiffOn (𝓡 3) (𝓡 3) ∞ ψ U →
          (∀ x ∈ U, (ψ x).val = (extChartAt (𝓡 3) q).symm x) →
          (∀ x ∈ U, (mfderiv (𝓡 3) (𝓡 3) ψ x).IsInvertible) →
          ∀ K, IsCompact K → K ⊆ U →
            ∃ alpha beta : ℝ, 0 < alpha ∧ 0 ≤ beta ∧
              (∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K, ∀ v,
                alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients ψ x v v ∧
                  ((P k).metric t).pullbackCoefficients ψ x v v ≤ beta * ‖v‖ ^ 2) ∧
              ∀ m : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ k : ℕ in atTop,
                ∀ z ∈ Icc (-tau) 0 ×ˢ K,
                  ‖iteratedFDerivWithin ℝ m
                    (fun z => ((P k).metric z.1).pullbackCoefficients ψ z.2)
                    (Icc (-tau) 0 ×ˢ U) z‖ ≤ B := by
  intro Y P hterminal hcurv q U hU hUc ψ hψ hψval hi K hK hKU
  let E := EuclideanSpace ℝ (Fin 3)
  let : NormedAddCommGroup (E →L[ℝ] ℝ) := ContinuousLinearMap.toNormedAddCommGroup
  let : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
    ContinuousLinearMap.toNormedAddCommGroup
  let c := extChartAt (𝓡 3) q
  let B0 := G.limitMetric.pullbackCoefficients c.symm
  have hchart {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K) :
      ContMDiffAt (𝓡 3) (𝓡 3) ∞ c.symm x :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) q (hUc (hKU hx))).contMDiffAt
      (extChartAt_target_mem_nhds' (hUc (hKU hx)))
  have hBdiff {x : EuclideanSpace ℝ (Fin 3)} (hx : x ∈ K) :
      ContDiffAt ℝ ∞ B0 x := G.limitMetric.contDiffAt_pullbackCoefficients (hchart hx)
  have hBcont : ContinuousOn B0 K :=
    fun _ hx => (hBdiff hx).continuousAt.continuousWithinAt
  have hpos : ∀ x ∈ K, ∀ v : EuclideanSpace ℝ (Fin 3), v ≠ 0 → 0 < B0 x v v := by
    intro x hx v hv
    apply G.limitMetric.pos
    have hinv : (mfderiv (𝓡 3) (𝓡 3) c.symm x).IsInvertible := by
      simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
        isInvertible_mfderivWithin_extChartAt_symm (hUc (hKU hx))
    intro hz
    apply hv
    apply hinv.injective
    rw [map_zero]
    convert! hz using 1
  have hjets (m : ℕ) := G.tendstoUniformlyOn_static_stage_metric_jets j N
    (fun k => (P k).metric 0) hterminal q U hU hUc ψ hψ hψval m K hK hKU
  have hcoeff : TendstoUniformlyOn
      (fun k => ((P k).metric 0).pullbackCoefficients ψ) B0 atTop K := by
    have h := (ContinuousMultilinearMap.uniformContinuous_eval_const
      (0 : Fin 0 → EuclideanSpace ℝ (Fin 3))).comp_tendstoUniformlyOn (hjets 0)
    simpa only [Function.comp_def, iteratedFDeriv_zero_apply] using! h
  obtain ⟨a, ha, hlower⟩ := exists_uniform_bilinear_family_lower_bound hK hBcont hpos
  obtain ⟨b, hb, hnorm⟩ := hcoeff.exists_eventual_norm_bound hK hBcont
  have hterm : ∀ᶠ k : ℕ in atTop, ∀ x ∈ K, ∀ v,
      (a / 2) * ‖v‖ ^ 2 ≤ ((P k).metric 0).pullbackCoefficients ψ x v v ∧
        ((P k).metric 0).pullbackCoefficients ψ x v v ≤ b * ‖v‖ ^ 2 := by
    filter_upwards [Metric.tendstoUniformlyOn_iff.mp hcoeff (a / 2) (by positivity), hnorm]
      with k hk hkn x hx v
    let Bk := ((P k).metric 0).pullbackCoefficients ψ
    have hdelta : ‖Bk x - B0 x‖ ≤ a / 2 := by
      simpa only [dist_eq_norm, norm_sub_rev] using (hk x hx).le
    have herr : |Bk x v v - B0 x v v| ≤ (a / 2) * ‖v‖ ^ 2 := by
      calc
        |Bk x v v - B0 x v v| ≤ ‖Bk x - B0 x‖ * (‖v‖ * ‖v‖) := by
          simpa only [sub_apply, Real.norm_eq_abs, mul_assoc] using
            (Bk x - B0 x).le_opNorm₂ v v
        _ ≤ (a / 2) * ‖v‖ ^ 2 := by
          simpa only [pow_two] using
            mul_le_mul_of_nonneg_right hdelta (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    constructor
    · nlinarith [hlower x hx v, (abs_le.mp herr).1]
    · apply (le_abs_self _).trans
      calc
        |Bk x v v| ≤ ‖Bk x‖ * (‖v‖ * ‖v‖) := by
          simpa only [Real.norm_eq_abs, mul_assoc] using (Bk x).le_opNorm₂ v v
        _ ≤ b * ‖v‖ ^ 2 := by
          simpa only [pow_two] using
            mul_le_mul_of_nonneg_right (hkn x hx) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  obtain ⟨D, hD, hDcurv⟩ := hcurv 0
  let alpha := Real.exp (-2 * (3 : ℝ) * D * tau) * (a / 2)
  let beta := Real.exp (2 * (3 : ℝ) * D * tau) * b
  have halpha : 0 < alpha := by dsimp [alpha]; positivity
  have hbeta : 0 ≤ beta := mul_nonneg (Real.exp_pos _).le (by linarith)
  have hell : ∀ᶠ k : ℕ in atTop, ∀ t ∈ Icc (-tau) 0, ∀ x ∈ K, ∀ v,
      alpha * ‖v‖ ^ 2 ≤ ((P k).metric t).pullbackCoefficients ψ x v v ∧
        ((P k).metric t).pullbackCoefficients ψ x v v ≤ beta * ‖v‖ ^ 2 := by
    filter_upwards [hterm] with k hk t ht x hx v
    exact M28.backward_pullback_ellipticity (P k) htau hD ψ x
      (fun s hs => by
        simpa only [LeviCivitaData.curvatureDerivativeNorm_zero] using hDcurv k s hs (ψ x))
      (hk x hx) ht v
  refine ⟨alpha, beta, halpha, hbeta, hell, ?_⟩
  apply M28.eventually_within_bounds_closed_backward_of_curvature atTop htau P
    (fun _ => U) (fun _ => K) (fun _ => ψ) (fun _ => hU) (fun _ => hKU)
    (fun _ => hψ) (fun _ => hi) halpha hbeta hell
  · intro m
    obtain ⟨D, hD, hbound⟩ := hcurv m
    exact ⟨D, hD, Eventually.of_forall fun k t ht x _ =>
      hbound k t (Ioo_subset_Icc_self ht) (ψ x)⟩
  · intro m
    have hcont : ContinuousOn (iteratedFDeriv ℝ m B0) K := fun x hx =>
      ((hBdiff hx).continuousAt_iteratedFDeriv
        (by exact_mod_cast le_top : (m : ℕ∞ω) ≤ ∞)).continuousWithinAt
    obtain ⟨Z, hZ, hbound⟩ := (hjets m).exists_eventual_norm_bound hK hcont
    exact ⟨Z, by linarith, hbound⟩

end PoincareConjecture.M30.PartialPointedMetricConvergence
