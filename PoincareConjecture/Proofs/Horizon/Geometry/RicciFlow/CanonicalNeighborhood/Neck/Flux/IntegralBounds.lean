import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.LowerBound
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.ProfileSupport
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Bounds

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace PoincareConjecture.EpsilonNeck

section Topological

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

theorem integral_flux_bounds_of_pointwise
    (N : EpsilonNeck g) {L κ₁ κ₂ : ℝ}
    (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    (hκ₁ : 0 ≤ κ₁) (hκ₂ : 0 ≤ κ₂) {Q : M → ℝ}
    (hQ : IntegrableOn Q N.carrier g.volumeMeasure)
    (hpoint : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      κ₁ * deriv (axialTransitionProfile L) (N.coordinate_inverse x).2 ≤ Q x ∧
      Q x ≤ κ₂ * deriv (axialTransitionProfile L) (N.coordinate_inverse x).2) :
    (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal * κ₁) ≤
      ∫ x in N.carrier, Q x ∂g.volumeMeasure ∧
    (∫ x in N.carrier, Q x ∂g.volumeMeasure) ≤
      (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal * κ₂) := by
  have hr := N.scale_pos.le
  have hderiv := ((contDiff_axialTransitionProfile L).continuous_deriv (by simp)).measurable
  have hnonneg : 0 ≤ᵐ[g.volumeMeasure.restrict N.carrier] Q := by
    filter_upwards [hpoint] with x hx
    exact (mul_nonneg hκ₁ (deriv_axialTransitionProfile_nonneg hL _)).trans hx.1
  have hI0 : 0 ≤ ∫ x in N.carrier, Q x ∂g.volumeMeasure := integral_nonneg_of_ae hnonneg
  have hconvert := ofReal_integral_eq_lintegral_ofReal hQ hnonneg
  have hlow := N.lintegral_flux_lower_of_pointwise hderiv
    (hpoint.mono fun _ h => h.1)
  rw [lintegral_ofReal_mul_deriv_axialTransitionProfile_of_le hL hLe hκ₁,
    ← hconvert] at hlow
  have hupp := (N.lintegral_axial_profile_bounds
    ((hderiv.const_mul κ₂).ennreal_ofReal)).2
  have hmono : (∫⁻ x in N.carrier, ENNReal.ofReal (Q x) ∂g.volumeMeasure) ≤
      ∫⁻ x in N.carrier,
        ENNReal.ofReal (κ₂ * deriv (axialTransitionProfile L)
          (N.coordinate_inverse x).2) ∂g.volumeMeasure := by
    apply lintegral_mono_ae
    filter_upwards [hpoint] with x hx
    exact ENNReal.ofReal_le_ofReal hx.2
  have hupp' := hmono.trans hupp
  rw [lintegral_ofReal_mul_deriv_axialTransitionProfile_of_le hL hLe hκ₂,
    ← hconvert] at hupp'
  have hfactor (a κ : ℝ) (ha : 0 ≤ a) :
      ENNReal.ofReal (a ^ 3 * (roundCylinderCrossSectionArea.toReal * κ)) =
        ENNReal.ofReal a ^ 3 * (roundCylinderCrossSectionArea * ENNReal.ofReal κ) := by
    rw [ENNReal.ofReal_mul (pow_nonneg ha _), ENNReal.ofReal_pow ha,
      ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal roundCylinderCrossSectionArea_lt_top.ne]
  constructor
  · apply (ENNReal.ofReal_le_ofReal_iff hI0).mp
    rw [hfactor _ _ (by positivity)]
    exact hlow
  · apply (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp
    rw [hfactor _ _ (by positivity)]
    exact hupp'

end Topological

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

theorem integral_abs_busemann_axialTransitionProfile_flux_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Poincare.Riemannian.Soul.IsRay ray)
    {L : ℝ} (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    (hI : IntegrableOn (fun x => mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
        N.carrier g.volumeMeasure) :
    (∫ x in N.carrier, |mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x)| ∂g.volumeMeasure) ≤
      (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal *
          (N.scale * Real.sqrt (1 - N.epsilon))⁻¹) := by
  have hscale := N.scale_pos.le
  apply (N.integral_flux_bounds_of_pointwise hL hLe (κ₁ := 0) le_rfl
    (by positivity) hI.abs ?_).2
  have hbound := N.ae_abs_busemann_axialCutoff_flux_le D hc hdist hray
    (contDiff_axialTransitionProfile L)
  filter_upwards [ae_restrict_of_ae hbound,
    ae_restrict_mem N.carrier_open.measurableSet] with x hx hxc
  constructor
  · simpa only [zero_mul] using abs_nonneg _
  · simpa only [abs_of_nonneg (deriv_axialTransitionProfile_nonneg hL _),
      mul_comm] using hx hxc

end PoincareConjecture.EpsilonNeck
