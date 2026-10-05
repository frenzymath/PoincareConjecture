import PoincareLib.Geometry.RicciFlow.ReducedGeometry.ReducedLength.Barrier.PathComparison

/-!
# Restricting the actual joint-seed path

All time, regularity and integrability fields are inherited from the
literal path. Nonnegative scalar curvature compares the two actions.
Source: Definition 6.2, p. 106, and Definition 6.45, p. 129.
See `proof-work/tasks/M47/derivations/joint-seed.md`, Stage B.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareMT.M47

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {J : Set ℝ} {F : RicciFlow n M J} {T tau theta : ℝ}

/-- Restriction preserves the actual curve and all admissibility fields
of a backward path; Definition 6.2, p. 106. -/
def jointSeed_restrict_path (path : BackwardTimePath F T 0 tau)
    (htheta : 0 < theta) (hle : theta ≤ tau) : BackwardTimePath F T 0 theta where
  curve := path.curve
  nonnegative := le_rfl
  ordered := htheta
  terminal_mem := path.terminal_mem
  time_mem := fun s hs => path.time_mem s ⟨hs.1, hs.2.trans hle⟩
  continuous := path.continuous.mono (Icc_subset_Icc le_rfl hle)
  regular := path.regular.mono (Ioo_subset_Ioo le_rfl hle)
  l_integrable := path.l_integrable.mono_set (by
    rw [uIcc_of_le htheta.le, uIcc_of_le path.ordered.le]
    exact Icc_subset_Icc le_rfl hle)

/-- The literal scalar-plus-kinetic integrand is nonnegative along an
actual path in a scalar-nonnegative flow; Definition 6.2, p. 106. -/
theorem jointSeed_integrand_nonneg (path : BackwardTimePath F T 0 tau)
    (hscalar : ∀ s ∈ J, ∀ x : M, 0 ≤ (F.connection s).scalarCurvature x)
    {s : ℝ} (hs : s ∈ Icc 0 tau) : 0 ≤ backwardLIntegrand F T path.curve s := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric (T - s)).toRiemannianMetric⟩
  have hkin : 0 ≤ (F.metric (T - s)).inner (path.curve s)
      (curveVelocity (n := n) path.curve s) (curveVelocity (n := n) path.curve s) := by
    change 0 ≤ inner ℝ (curveVelocity (n := n) path.curve s)
      (curveVelocity (n := n) path.curve s)
    exact real_inner_self_nonneg
  exact mul_nonneg (Real.sqrt_nonneg s)
    (add_nonneg (hscalar (T - s) (path.time_mem s hs) (path.curve s)) hkin)

/-- Removing the terminal part of a backward path can only decrease
its action under scalar nonnegativity; Definitions 6.2 and 6.45. -/
theorem jointSeed_restricted_action_le (path : BackwardTimePath F T 0 tau)
    (htheta : 0 < theta) (hle : theta ≤ tau)
    (hscalar : ∀ s ∈ J, ∀ x : M, 0 ≤ (F.connection s).scalarCurvature x) :
    backwardLLength F T 0 theta (jointSeed_restrict_path path htheta hle).curve ≤
      backwardLLength F T 0 tau path.curve := by
  apply intervalIntegral.integral_mono_interval le_rfl htheta.le hle
    ?_ path.l_integrable
  exact (ae_restrict_mem measurableSet_Ioc).mono (fun s hs =>
    jointSeed_integrand_nonneg path hscalar ⟨hs.1.le, hs.2⟩)

end PoincareMT.M47
