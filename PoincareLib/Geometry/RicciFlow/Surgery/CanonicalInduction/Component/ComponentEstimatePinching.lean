import PoincareLib.Topology.Manifold.Poincare.Final.Compatibility.SourceNames
import PoincareLib.Geometry.RicciFlow.Surgery.CanonicalInduction.Seed.Volume.SeedVolume

/-!
# Pinching on the stopped component history

The proved M46 scalar-to-full-curvature estimate applies with the identical
services already supplied to M47. It gives a fixed full-curvature coefficient
after rescaling a component whose scalar is bounded above by LQ. Source:
Corollary 4.33, p. 80, in the first-failure argument, pp. 402-405.
See `proof-work/tasks/M47/derivations/component-estimate.md`, Stage D1.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareMT.M47

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  {g : RiemannianMetric 3 M} {D : LeviCivitaData g}

/-- On the stopped scalar-controlled component, pinching gives the
uniform full-curvature coefficient thirteen; Corollary 4.33, p. 80. -/
theorem component_pinched_curvature_bound (P : M47Predecessors.{u})
    {t Q L : ℝ} {U : Set M} (hpinch : SurgeryPinchedOn D t U)
    (hQ : Real.exp 4 ≤ Q) (hL : 1 ≤ L) {x : M} (hx : x ∈ U)
    (hscalar : D.scalarCurvature x ≤ L * Q) :
    D.curvatureTensorNorm x ≤ 13 * (L * Q) := by
  have hQpos : 0 < Q := (Real.exp_pos 4).trans_le hQ
  have hQL : Q ≤ L * Q := by nlinarith
  exact (Proofs.M46.pinched_curvature_norm_le P.toM46 hpinch hx).trans
    (mul_le_mul_of_nonneg_left (max_le hscalar (hQ.trans hQL)) (by norm_num))

/-- Absolute pinching supplies the scalar floor used before rescaling;
Definition 4.30 and Corollary 4.33, pp. 79-80. -/
theorem component_pinched_scalar_floor {t : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) {x : M} (hx : x ∈ U) :
    -6 ≤ D.scalarCurvature x := by
  have hden : 0 < 1 + 4 * t := by linarith [hpinch.1]
  have hfloor : (-6 : ℝ) ≤ -6 / (1 + 4 * t) := by
    apply (le_div_iff₀ hden).2
    nlinarith [hpinch.1]
  exact hfloor.trans (hpinch.2.1 x hx)

/-- In LQ units the pinched scalar is at least minus one once Q is
at least six; this is the floor for local scalar persistence. -/
theorem component_pinched_scaled_scalar_floor {t Q L : ℝ} {U : Set M}
    (hpinch : SurgeryPinchedOn D t U) (hQ : 6 ≤ Q) (hL : 1 ≤ L)
    {x : M} (hx : x ∈ U) : -(L * Q) ≤ D.scalarCurvature x := by
  have hQL : 6 ≤ L * Q := by nlinarith
  exact (by linarith : -(L * Q) ≤ -6).trans (component_pinched_scalar_floor hpinch hx)

end PoincareMT.M47
