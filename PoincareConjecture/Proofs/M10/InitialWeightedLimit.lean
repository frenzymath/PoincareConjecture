import PoincareConjecture.Proofs.M10.InitialGram
import PoincareConjecture.Proofs.M10.InitialActionLimit
import PoincareConjecture.Proofs.M10.WeightedRays









set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Bundle Topology

universe u

namespace PoincareConjecture.M10

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M] [T3Space M]
  {J : Set ℝ} {F : RicciFlow n M J} {T τmax : ℝ} {p : M}

set_option backward.isDefEq.respectTransparency false in

theorem weightedExponentialJacobian_tendsto_initial
    (G : LExponentialGeometry F T τmax p) (hmax : 0 < τmax)
    (hT : T ∈ J) (hwindow : Icc (T - τmax) T ⊆ J)
    (hcurvature : CompleteBoundedCurvatureOn F (Icc (T - τmax) T))
    (x : EuclideanSpace ℝ (Fin n)) :
    Tendsto (fun τ : ℝ ↦ weightedExponentialJacobian G τ x) (𝓝[>] (0 : ℝ))
      (𝓝 ((2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))) := by
  have hA := squareAction_quotient_tendsto G hmax hT hwindow hcurvature
    (metricCoordinates (F.metric T) p x)
  rw [metricCoordinates_inner, real_inner_self_eq_norm_sq] at hA
  have hJ := exponential_scaled_jacobian_tendsto G hmax hT hwindow x
  have hprod := hJ.mul (Real.continuous_exp.continuousAt.tendsto.comp hA.neg)
  have hsquare : Tendsto (fun s : ℝ ↦ weightedExponentialJacobian G (s ^ 2) x)
      (𝓝[>] (0 : ℝ)) (𝓝 ((2 : ℝ) ^ n * Real.exp (-‖x‖ ^ 2))) := by
    apply hprod.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hpow : Real.rpow (s ^ 2) (-(n : ℝ) / 2) = (s ^ n)⁻¹ := by
      rw [Real.rpow_eq_pow, ← Real.rpow_natCast_mul hs.le 2]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 : ℝ) * (-(n : ℝ) / 2) = -(n : ℝ) by ring,
        Real.rpow_neg hs.le, Real.rpow_natCast]
    simp only [weightedExponentialJacobian, hpow, Real.sqrt_sq hs.le, Function.comp_def]
    ring
  have hsqrt : Tendsto Real.sqrt (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa only [Real.sqrt_zero] using
        (Real.continuous_sqrt.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact Real.sqrt_pos.2 hs
  apply (hsquare.comp hsqrt).congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  simp only [Function.comp_def, Real.sq_sqrt hs.le]

end PoincareConjecture.M10
