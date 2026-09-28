import PoincareConjecture.Proofs.M10.SquareAction
import PoincareConjecture.Proofs.M10.ScalarBound
import PoincareConjecture.Proofs.M10.InitialActionContinuity
import PoincareConjecture.Proofs.M10.MetricTrace
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Asymptotics.Lemmas










set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem squareAction_quotient_tendsto (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (Z : TangentSpace (𝓡 n) p) :
    Tendsto (fun s : ℝ ↦ G.toLExponentialFamily.action Z (s ^ 2) / (2 * s))
      (𝓝[>] (0 : ℝ)) (𝓝 ((F.metric T).inner p Z Z)) := by
  let R := fun s : ℝ ↦ (F.connection (T - s ^ 2)).scalarCurvature (G.gamma Z (s ^ 2))
  let H' := fun s : ℝ ↦ 2 * s ^ 2 * R s + squareKineticEnergy G Z s / 2
  have hsq : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).pow 2
  have hsqpos : Tendsto (fun s : ℝ ↦ s ^ 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨hsq, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact sq_pos_of_pos (show (0 : ℝ) < s from hs)
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo 0 (Real.sqrt τmax) :=
    Ioo_mem_nhdsGT (Real.sqrt_pos.2 hmax)
  obtain ⟨C, _, hC⟩ := exists_uniform_scalarCurvature_bound F hcurvature
  have hbound : IsBoundedUnder (· ≤ ·) (𝓝[>] (0 : ℝ)) (norm ∘ R) := by
    apply isBoundedUnder_of_eventually_le (a := C)
    filter_upwards [hsmall] with s hs
    have hsmax : s ^ 2 < τmax := by nlinarith [Real.sq_sqrt hmax.le, hs.1, hs.2]
    have ht : T - s ^ 2 ∈ Icc (T - τmax) T := by
      constructor <;> nlinarith [sq_nonneg s]
    simpa only [Function.comp_def, Real.norm_eq_abs, R] using hC (T - s ^ 2) ht _
  have hR : Tendsto (fun s : ℝ ↦ s ^ 2 * R s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply] using!
      NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hsq hbound
  have hK := squareKineticEnergy_tendsto_zero G hmax hT hwindow Z
  have hratio : Tendsto (fun s : ℝ ↦ H' s / 2) (𝓝[>] (0 : ℝ))
      (𝓝 ((F.metric T).inner p Z Z)) := by
    convert hR.add (hK.div_const 4) using 1
    · funext s
      dsimp only [H']
      ring
    · congr 1
      ring
  have hchart : ∀ᶠ s in 𝓝[>] (0 : ℝ), G.squareFamily Z s ∈
      (chartAt (EuclideanSpace ℝ (Fin n)) p).source :=
    ((squareFamily_tendsto_zero G hmax Z).mono_left nhdsWithin_le_nhds)
      ((chartAt (EuclideanSpace ℝ (Fin n)) p).open_source.mem_nhds (mem_chart_source _ _))
  have hH : ∀ᶠ s in 𝓝[>] (0 : ℝ),
      HasDerivAt (fun r : ℝ ↦ G.toLExponentialFamily.action Z (r ^ 2)) (H' s) s := by
    filter_upwards [hsmall, hchart] with s hs hq
    rw [G.square_agrees Z s ⟨hs.1.le, hs.2⟩] at hq
    exact squareAction_hasDerivAt G hmax Z hs hq
  have hg : ∀ᶠ s in 𝓝[>] (0 : ℝ), HasDerivAt (fun r : ℝ ↦ 2 * r) 2 s :=
    Filter.Eventually.of_forall (fun s ↦ by simpa using (hasDerivAt_id s).const_mul 2)
  have hgzero : Tendsto (fun s : ℝ ↦ 2 * s) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using ((tendsto_id : Tendsto (id : ℝ → ℝ) (𝓝 0) (𝓝 0)).mono_left
      nhdsWithin_le_nhds).const_mul 2
  exact HasDerivAt.lhopital_zero_nhdsGT hH hg (Filter.Eventually.of_forall (by norm_num))
    ((action_tendsto_zero G hmax Z).comp hsqpos) hgzero hratio


theorem normalized_action_tendsto_initial (G : LExponentialGeometry F T τmax p)
    (hmax : 0 < τmax) (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun τ : ℝ ↦ G.toLExponentialFamily.action
      (metricCoordinates (F.metric T) p x) τ / (2 * Real.sqrt τ))
      (𝓝[>] (0 : ℝ)) (𝓝 (‖x‖ ^ 2)) := by
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.2 hs
  have h := (squareAction_quotient_tendsto G hmax hT hwindow hcurvature
    (metricCoordinates (F.metric T) p x)).comp hsqrt
  rw [metricCoordinates_inner, real_inner_self_eq_norm_sq] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_def, Real.sq_sqrt hs.le]

end PoincareConjecture.M10
