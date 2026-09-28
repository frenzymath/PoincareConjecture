import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Directional
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.IntegralBounds.Oriented











noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}



theorem integral_neg_outward_axialTransition_flux_lower_of_gradient_distance
    (N : EpsilonNeck g) (D : LeviCivitaData g) (A : Set M)
    {f : M → ℝ} {L σ : ℝ} {ψ : ℝ → ℝ}
    (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    (hkind : (σ = -1 ∧ ψ = axialTransitionProfile L) ∨
      (σ = 1 ∧ ψ = fun s => 1 - axialTransitionProfile L s))
    (hclose : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      (N.coordinate_inverse x).2 ∈ Ioo (-L) L →
      ∃ a : TangentSpace (𝓡 3) x,
        g.tangentNorm x (σ • D.gradient f x - a) ≤ 1 / 4 ∧
        mvfderiv (𝓡 3) (fun y => (N.coordinate_inverse y).2) x a = N.scale⁻¹)
    (hI : IntegrableOn (fun x => mvfderiv (𝓡 3) f x
      (D.gradient (N.axialTransition A ψ) x)) N.carrier g.volumeMeasure) :
    (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
      (roundCylinderCrossSectionArea.toReal *
        (N.scale⁻¹ - (1 / 4 : ℝ) / (N.scale * Real.sqrt (1 - N.epsilon)))) ≤
      -(∫ x in N.carrier, mvfderiv (𝓡 3) f x
        (D.gradient (N.axialTransition A ψ) x) ∂g.volumeMeasure) := by
  have hsqrt : 0 < Real.sqrt (1 - N.epsilon) :=
    Real.sqrt_pos.mpr (by linarith [N.epsilon_lt_half])
  have hsqrt_sq : Real.sqrt (1 - N.epsilon) ^ 2 = 1 - N.epsilon :=
    Real.sq_sqrt (by linarith [N.epsilon_lt_half])
  have hsqrt_half : 1 / 2 ≤ Real.sqrt (1 - N.epsilon) := by
    nlinarith [N.epsilon_lt_half, sq_nonneg (Real.sqrt (1 - N.epsilon) - 1 / 2)]
  have hκ : 0 ≤ N.scale⁻¹ - (1 / 4 : ℝ) / (N.scale * Real.sqrt (1 - N.epsilon)) := by
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (mul_pos N.scale_pos hsqrt)).mpr
    rw [← mul_assoc, inv_mul_cancel₀ N.scale_pos.ne', one_mul]
    linarith
  have heq : (fun x => σ * mvfderiv (𝓡 3) f x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
      =ᵐ[g.volumeMeasure.restrict N.carrier]
      fun x => -mvfderiv (𝓡 3) f x (D.gradient (N.axialTransition A ψ) x) := by
    filter_upwards [ae_restrict_mem N.carrier_open.measurableSet] with x hx
    rcases hkind with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rw [N.gradient_axialTransition_eq_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx, neg_one_mul]
    · rw [N.gradient_axialTransition_one_sub_eq_neg_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx, map_neg, neg_neg, one_mul]
  have hbase : IntegrableOn (fun x => σ * mvfderiv (𝓡 3) f x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
      N.carrier g.volumeMeasure := hI.neg.congr heq.symm
  have h := N.integral_axialTransitionProfile_flux_lower_of_gradient_distance
    D hL hLe hκ hclose hbase
  rwa [integral_congr_ae heq, integral_neg] at h

end PoincareConjecture.EpsilonNeck
