import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Volume
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Profile
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.BusemannGradient











noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle ENNReal Topology
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



omit [MetricSpace M] in
theorem lintegral_flux_lower_of_pointwise
    {F : ℝ → ℝ} (hF : Measurable F)
    {κ : ℝ}
    {Q : M → ℝ}
    (hpoint : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      κ * F (N.coordinate_inverse x).2 ≤ Q x) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea *
          ∫⁻ t in Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
            ENNReal.ofReal (κ * F t)) ≤
      ∫⁻ x in N.carrier, ENNReal.ofReal (Q x) ∂g.volumeMeasure := by
  have hFκ : Measurable (fun t : ℝ => κ * F t) := hF.const_mul κ
  have hprofile : Measurable (fun t : ℝ => ENNReal.ofReal (κ * F t)) :=
    hFκ.ennreal_ofReal
  have hvolume := N.lintegral_axial_profile_bounds hprofile
  have hmono :
      (∫⁻ x in N.carrier,
          ENNReal.ofReal (κ * F (N.coordinate_inverse x).2) ∂g.volumeMeasure) ≤
        ∫⁻ x in N.carrier, ENNReal.ofReal (Q x) ∂g.volumeMeasure := by
    apply lintegral_mono_ae
    filter_upwards [hpoint] with x hx
    exact ENNReal.ofReal_le_ofReal hx
  exact hvolume.1.trans hmono




theorem lintegral_busemann_axialCutoff_flux_lower
    (D : LeviCivitaData g) {ray : ℝ → M} {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ ∞ φ) {κ : ℝ}
    (hpoint : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      κ * deriv φ (N.coordinate_inverse x).2 ≤
        mvfderiv (𝓡 3) (busemann ray) x
          (D.gradient (N.axialCutoff φ) x)) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea *
          ∫⁻ t in Ioo (-N.epsilon⁻¹) N.epsilon⁻¹,
            ENNReal.ofReal (κ * deriv φ t)) ≤
      ∫⁻ x in N.carrier, ENNReal.ofReal
        (mvfderiv (𝓡 3) (busemann ray) x
          (D.gradient (N.axialCutoff φ) x)) ∂g.volumeMeasure := by
  apply N.lintegral_flux_lower_of_pointwise
    ((hφ.continuous_deriv (by simp)).measurable) hpoint



theorem lintegral_busemann_axialTransitionProfile_flux_lower
    (D : LeviCivitaData g) {ray : ℝ → M} {κ : ℝ} (hκ : 0 ≤ κ)
    (hpoint : ∀ᵐ x ∂(g.volumeMeasure.restrict N.carrier),
      κ * deriv (axialTransitionProfile N.epsilon⁻¹)
          (N.coordinate_inverse x).2 ≤
        mvfderiv (𝓡 3) (busemann ray) x
          (D.gradient (N.axialCutoff (axialTransitionProfile N.epsilon⁻¹)) x)) :
    ENNReal.ofReal (N.scale * Real.sqrt (1 - N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea * ENNReal.ofReal κ) ≤
      ∫⁻ x in N.carrier, ENNReal.ofReal
        (mvfderiv (𝓡 3) (busemann ray) x
          (D.gradient (N.axialCutoff (axialTransitionProfile N.epsilon⁻¹)) x))
        ∂g.volumeMeasure := by
  have hφ : ContDiff ℝ ∞ (axialTransitionProfile N.epsilon⁻¹) :=
    contDiff_axialTransitionProfile _
  have h := N.lintegral_busemann_axialCutoff_flux_lower D hφ hpoint
  rw [lintegral_ofReal_mul_deriv_axialTransitionProfile
    (inv_pos.mpr N.epsilon_pos) hκ] at h
  exact h

end PoincareConjecture.EpsilonNeck
