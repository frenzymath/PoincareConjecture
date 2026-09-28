import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Axial
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.BusemannGradient
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Flux.Cutoff










set_option autoImplicit false

open Set Filter MeasureTheory
open scoped Manifold ContDiff Bundle Topology
open Poincare.Riemannian.Soul

namespace PoincareConjecture.EpsilonNeck

variable {M : Type*} [MetricSpace M] [T3Space M] [ConnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M]
  {g : RiemannianMetric 3 M} (N : EpsilonNeck g)



theorem ae_abs_busemann_axial_flux_le
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray) :
    ∀ᵐ x ∂g.volumeMeasure, x ∈ N.carrier →
      |mvfderiv (𝓡 3) (busemann ray) x
        (D.gradient (fun y => (N.coordinate_inverse y).2) x)| ≤
        (N.scale * Real.sqrt (1 - N.epsilon))⁻¹ := by
  filter_upwards [g.ae_ray_busemann_gradient_norm_eq_one D hc hdist hray] with x hx
  intro hxc
  calc
    _ ≤ g.tangentNorm x (D.gradient (busemann ray) x) *
        g.tangentNorm x (D.gradient (fun y => (N.coordinate_inverse y).2) x) :=
      D.abs_mvfderiv_le_gradient_norm _ _ _
    _ = g.tangentNorm x (D.gradient (fun y => (N.coordinate_inverse y).2) x) := by
      rw [hx, one_mul]
    _ ≤ _ := N.axial_gradient_norm_le D hxc



theorem ae_abs_busemann_axialCutoff_flux_le
    (D : LeviCivitaData g) (hc : MetricComplete g)
    (hdist : ∀ x y : M, dist x y = (g.edist x y).toReal)
    {ray : ℝ → M} (hray : IsRay ray)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) :
    ∀ᵐ x ∂g.volumeMeasure, x ∈ N.carrier →
      |mvfderiv (𝓡 3) (busemann ray) x (D.gradient (N.axialCutoff φ) x)| ≤
        |deriv φ (N.coordinate_inverse x).2| *
          (N.scale * Real.sqrt (1 - N.epsilon))⁻¹ := by
  filter_upwards [N.ae_abs_busemann_axial_flux_le D hc hdist hray] with x hx
  intro hxc
  rw [N.gradient_axialCutoff D hφ hxc, map_smul, smul_eq_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left (hx hxc) (abs_nonneg _)

end PoincareConjecture.EpsilonNeck
