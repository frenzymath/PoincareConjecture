import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.Closed
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.Noncollapse.Universal.Rescaling.ReducedLength
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.AncientKappa.AsymptoticSoliton
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Measure.Basic










noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.AncientRescaling

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} {tau : ℝ} (R : AncientRescaling K tau)
  (W : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow tau⁻¹
    (inv_pos.mpr R.tau_pos) 0)

def closedExtension : AncientKappaSolution n M :=
  K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W

theorem closedExtension_metric_eq (t : ℝ) (ht : t < 0) :
    (R.closedExtension W).flow.metric t = R.flow.metric t := by
  have hinner : ((R.closedExtension W).flow.metric t).inner = (R.flow.metric t).inner := by
    funext x
    apply ContinuousLinearMap.ext
    intro v
    apply ContinuousLinearMap.ext
    intro w
    rw [R.metric_scale t ht]
    change ((K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W).flow.metric t).inner x v w = _
    rw [K.closedRescale_metric_inner]
    simp only [zero_add, div_inv_eq_mul, one_div, mul_comm t tau]
  generalize (R.closedExtension W).flow.metric t = g₁ at hinner ⊢
  generalize R.flow.metric t = g₂ at hinner ⊢
  cases g₁
  cases g₂
  cases hinner
  rfl

theorem closedExtension_scalar (t : ℝ) (ht : t < 0) (x : M) :
    ((R.closedExtension W).flow.connection t).scalarCurvature x =
      (R.flow.connection t).scalarCurvature x := by
  rw [R.scalar_scale t ht]
  change ((K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W).flow.connection t).scalarCurvature x = _
  rw [K.closedRescale_scalar]
  rw [show 0 + t / tau⁻¹ = tau * t by simp [mul_comm], div_inv_eq_mul, mul_comm]

theorem closedExtension_curvature_norm (t : ℝ) (ht : t < 0) (x : M) :
    ((R.closedExtension W).flow.connection t).curvatureTensorNorm x =
      (R.flow.connection t).curvatureTensorNorm x := by
  rw [R.curvature_norm_scale t ht]
  change ((K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W).flow.connection t).curvatureTensorNorm x = _
  rw [K.closedRescale_curvature_norm]
  rw [show 0 + t / tau⁻¹ = tau * t by simp [mul_comm], div_inv_eq_mul, mul_comm]

theorem closedExtension_ball (t : ℝ) (ht : t < 0) (x : M) (r : ℝ) :
    ((R.closedExtension W).flow.metric t).ball x r = (R.flow.metric t).ball x r := by
  rw [R.closedExtension_metric_eq W t ht]

theorem closedExtension_volume (t : ℝ) (ht : t < 0) (A : Set M) :
    ((R.closedExtension W).flow.metric t).volumeMeasure A =
      (R.flow.metric t).volumeMeasure A := by
  rw [R.closedExtension_metric_eq W t ht]

theorem closedExtension_ball_volume (t : ℝ) (ht : t < 0) (x : M) (r : ℝ) :
    ((R.closedExtension W).flow.metric t).volumeMeasure
        (((R.closedExtension W).flow.metric t).ball x r) =
      (R.flow.metric t).volumeMeasure ((R.flow.metric t).ball x r) := by
  rw [R.closedExtension_metric_eq W t ht]

theorem closedExtension_closed_curvature_bound (p : M) (r : ℝ)
    (hcurv : ∀ s ∈ Icc (-(r ^ 2)) 0, ∀ x ∈ (K.flow.metric 0).ball p r,
      |(K.flow.connection s).curvatureTensorNorm x| ≤ r⁻¹ ^ 2) :
    ∀ s ∈ Icc (-((Real.sqrt tau⁻¹ * r) ^ 2)) 0,
      ∀ x ∈ ((R.closedExtension W).flow.metric 0).ball p (Real.sqrt tau⁻¹ * r),
        |((R.closedExtension W).flow.connection s).curvatureTensorNorm x| ≤
          (Real.sqrt tau⁻¹ * r)⁻¹ ^ 2 := by
  apply K.closedRescale_closed_curvature_bound (inv_pos.mpr R.tau_pos) le_rfl W p r
  simpa only [zero_sub] using hcurv

theorem closedExtension_ball_volume_lower_bound_iff (p : M) (r κ : ℝ) :
    (ENNReal.ofReal (κ * (Real.sqrt tau⁻¹ * r) ^ n) ≤
      calibratedMetricVolume ((R.closedExtension W).flow.metric 0)
        (((R.closedExtension W).flow.metric 0).ball p (Real.sqrt tau⁻¹ * r))) ↔
      ENNReal.ofReal (κ * r ^ n) ≤
        calibratedMetricVolume (K.flow.metric 0) ((K.flow.metric 0).ball p r) :=
  K.closedRescale_ball_volume_lower_bound_iff (inv_pos.mpr R.tau_pos) le_rfl W p r κ

theorem closedExtension_reducedLength {b : ℝ} (hb : 0 < b) (x y : M) :
    reducedLength (R.closedExtension W).flow 0 x y b =
      reducedLength K.flow 0 x y (tau * b) := by
  apply reducedLength_parabolicRescale R.tau_pos ?_ ?_ hb
  · intro t p v w
    change ((K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W).flow.metric t).inner p v w = _
    rw [K.closedRescale_metric_inner]
    rw [show 0 + t / tau⁻¹ = tau * t by simp [mul_comm]]
  · intro t p
    change ((K.closedRescale (inv_pos.mpr R.tau_pos) le_rfl W).flow.connection t).scalarCurvature p = _
    rw [K.closedRescale_scalar]
    rw [show 0 + t / tau⁻¹ = tau * t by simp [mul_comm], div_inv_eq_mul, mul_comm]

theorem closedExtension_reducedLength_one (x y : M) :
    reducedLength (R.closedExtension W).flow 0 x y 1 =
      reducedLength K.flow 0 x y tau := by
  simpa only [mul_one] using R.closedExtension_reducedLength W zero_lt_one x y

end PoincareConjecture.AncientRescaling

namespace PoincareConjecture.AncientRescalingSequence

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution n M} (S : AncientRescalingSequence K) (k : ℕ)
  (W : OrdinaryParabolicRescaling (I := closedAncientInterval) K.flow (S.scale k)⁻¹
    (inv_pos.mpr (S.rescaling k).tau_pos) 0)

theorem closedExtension_base_reduced_length_bound :
    reducedLength ((S.rescaling k).closedExtension W).flow 0 S.reference (S.base k) 1 ≤
      (n : ℝ) / 2 := by
  rw [(S.rescaling k).closedExtension_reducedLength_one]
  exact S.base_reduced_length_bound k

theorem normalized_radius_sq_eventually_le_two {subseq : ℕ → ℕ}
    (hsubseq : StrictMono subseq) (r : ℝ) :
    ∀ᶠ k in Filter.atTop, (Real.sqrt (S.scale (subseq k))⁻¹ * r) ^ 2 ≤ 2 := by
  have hscale := (S.scale_tendsto.comp hsubseq.tendsto_atTop).eventually_ge_atTop (r ^ 2)
  filter_upwards [hscale] with k hk
  change r ^ 2 ≤ S.scale (subseq k) at hk
  rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr (S.scale_pos _).le), inv_mul_eq_div]
  apply (div_le_iff₀ (S.scale_pos _)).mpr
  linarith [S.scale_pos (subseq k)]

end PoincareConjecture.AncientRescalingSequence
