import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.IntegralBounds
import PoincareLib.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff.Oriented

/-!
# Upper integral bounds for outward neck flux

An outward transition uses either the increasing axial profile or its
complement. On the neck carrier their gradients differ only by sign, so the
absolute flux has the same exact upper bound in either orientation.

Reference: Morgan--Tian, Proposition 2.19, pp. 31--32.
-/

noncomputable section
set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff

namespace PoincareMT.EpsilonNeck

section Topological

variable {M : Type*} [TopologicalSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

/-- Inside the carrier, the ambient transition and the axial cutoff have
the same gradient. -/
theorem gradient_axialTransition_eq_gradient_axialCutoff
    (N : EpsilonNeck g) (D : LeviCivitaData g) (A : Set M)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : M} (hx : x ∈ N.carrier) :
    D.gradient (N.axialTransition A φ) x = D.gradient (N.axialCutoff φ) x := by
  rw [N.gradient_axialTransition D A hφ hx, N.gradient_axialCutoff D hφ hx]

/-- Complementing the transition profile negates its gradient on the carrier. -/
theorem gradient_axialTransition_one_sub_eq_neg_gradient_axialCutoff
    (N : EpsilonNeck g) (D : LeviCivitaData g) (A : Set M)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) {x : M} (hx : x ∈ N.carrier) :
    D.gradient (N.axialTransition A (fun s => 1 - φ s)) x =
      -D.gradient (N.axialCutoff φ) x := by
  rw [N.gradient_axialTransition D A (contDiff_const.sub hφ) hx,
    N.gradient_axialCutoff D hφ hx,
    deriv_const_sub, neg_smul]

end Topological

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] {g : RiemannianMetric 3 M}

/-- The absolute flux upper bound is independent of which half of the neck
is the compact side. -/
theorem integral_abs_busemann_outward_axialTransition_flux_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Poincare.Riemannian.Soul.IsRay ray)
    (A : Set M) {L : ℝ} (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    {ψ : ℝ → ℝ}
    (hψ : ψ = axialTransitionProfile L ∨ ψ = fun s => 1 - axialTransitionProfile L s)
    (hI : IntegrableOn (fun x => mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialTransition A ψ) x)) N.carrier g.volumeMeasure) :
    (∫ x in N.carrier, |mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialTransition A ψ) x)| ∂g.volumeMeasure) ≤
      (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal *
          (N.scale * Real.sqrt (1 - N.epsilon))⁻¹) := by
  have heq : (fun x => |mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialTransition A ψ) x)|) =ᵐ[g.volumeMeasure.restrict N.carrier]
      fun x => |mvfderiv (𝓡 3) (Poincare.Riemannian.Soul.busemann ray) x
        (D.gradient (N.axialCutoff (axialTransitionProfile L)) x)| := by
    filter_upwards [ae_restrict_mem N.carrier_open.measurableSet] with x hx
    rcases hψ with rfl | rfl
    · rw [N.gradient_axialTransition_eq_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx]
    · rw [N.gradient_axialTransition_one_sub_eq_neg_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx, map_neg, abs_neg]
  have hbase : IntegrableOn (fun x => mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialCutoff (axialTransitionProfile L)) x))
      N.carrier g.volumeMeasure := by
    rcases hψ with rfl | rfl
    · apply hI.congr
      filter_upwards [ae_restrict_mem N.carrier_open.measurableSet] with x hx
      rw [N.gradient_axialTransition_eq_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx]
    · apply hI.neg.congr
      filter_upwards [ae_restrict_mem N.carrier_open.measurableSet] with x hx
      change -mvfderiv (𝓡 3) (Poincare.Riemannian.Soul.busemann ray) x
          (D.gradient (N.axialTransition A (fun s => 1 - axialTransitionProfile L s)) x) = _
      rw [N.gradient_axialTransition_one_sub_eq_neg_gradient_axialCutoff D A
        (contDiff_axialTransitionProfile L) hx, map_neg, neg_neg]
  rw [integral_congr_ae heq]
  exact N.integral_abs_busemann_axialTransitionProfile_flux_le D hc hdist hray hL hLe hbase

/-- The signed outward flux is bounded in absolute value by the same exact
metric and volume factors. -/
theorem abs_integral_busemann_outward_axialTransition_flux_le
    (N : EpsilonNeck g) (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : Poincare.Riemannian.Soul.IsRay ray)
    (A : Set M) {L : ℝ} (hL : 0 < L) (hLe : L ≤ N.epsilon⁻¹)
    {ψ : ℝ → ℝ}
    (hψ : ψ = axialTransitionProfile L ∨ ψ = fun s => 1 - axialTransitionProfile L s)
    (hI : IntegrableOn (fun x => mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialTransition A ψ) x)) N.carrier g.volumeMeasure) :
    |∫ x in N.carrier, mvfderiv (𝓡 3)
      (Poincare.Riemannian.Soul.busemann ray) x
      (D.gradient (N.axialTransition A ψ) x) ∂g.volumeMeasure| ≤
      (N.scale * Real.sqrt (1 + N.epsilon)) ^ 3 *
        (roundCylinderCrossSectionArea.toReal *
          (N.scale * Real.sqrt (1 - N.epsilon))⁻¹) := by
  exact abs_integral_le_integral_abs.trans
    (N.integral_abs_busemann_outward_axialTransition_flux_le D hc hdist hray A hL hLe hψ hI)

end PoincareMT.EpsilonNeck
