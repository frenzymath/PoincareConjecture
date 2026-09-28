import PoincareConjecture.Proofs.M07.Geometry.Riemannian.Comparison.Injectivity.Lifting.Bounded
import Mathlib.Topology.SeparatedMap












noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Function
open scoped Manifold ContDiff

namespace PoincareConjecture

variable {n : ℕ} {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]



theorem exists_finite_fiber_at_curve_endpoint
    (g : RiemannianMetric n M)
    {f : EuclideanSpace ℝ (Fin n) → M} {R C : ℝ}
    (hf : ContMDiffOn (𝓡 n) (𝓡 n) ∞ f (Metric.ball 0 R))
    (hbij : ∀ x ∈ Metric.ball 0 R, Function.Bijective (mfderiv (𝓡 n) (𝓡 n) f x))
    (hlower : ∀ x ∈ Metric.ball 0 R, ∀ w : EuclideanSpace ℝ (Fin n),
      ‖w‖ / 2 ≤ g.tangentNorm (f x) (mfderiv (𝓡 n) (𝓡 n) f x w))
    {c : ℝ → M} (hc : ∀ t ∈ Icc (0 : ℝ) 1, ContMDiffAt 𝓘(ℝ, ℝ) (𝓡 n) ∞ c t)
    (hC : 0 ≤ C)
    (hspeed : ∀ t ∈ Icc (0 : ℝ) 1, g.tangentNorm (c t)
      (mfderiv 𝓘(ℝ, ℝ) (𝓡 n) c t 1) ≤ C)
    {k : ℕ} (y : Fin k → EuclideanSpace ℝ (Fin n)) (hy : Injective y)
    (hyproj : ∀ i, f (y i) = c 0) (hshort : ∀ i, ‖y i‖ + 2 * C < R) :
    ∃ z : Fin k → EuclideanSpace ℝ (Fin n), Injective z ∧
      ∀ i, z i ∈ Metric.ball 0 R ∧ f (z i) = c 1 ∧ ‖z i - y i‖ ≤ 2 * C := by
  have hymem i : y i ∈ Metric.ball 0 R := by
    rw [Metric.mem_ball, dist_zero_right]
    exact (le_add_of_nonneg_right (show 0 ≤ 2 * C by positivity)).trans_lt (hshort i)
  choose l hl h0 hproj hbound using fun i =>
    exists_bounded_lift_of_lower_differential g hf hbij hlower hc hC hspeed
      ⟨y i, hymem i⟩ (hyproj i) (hshort i)
  refine ⟨fun i => l i 1, ?_, ?_⟩
  · intro i j hij
    have heq := (T2Space.isSeparatedMap ((Metric.ball (0 : EuclideanSpace ℝ (Fin n)) R).domRestrict f)).eqOn_of_comp_eqOn
      (isLocalHomeomorph_domRestrict_of_nonsingular Metric.isOpen_ball hf hbij).isLocallyInjective
      isPreconnected_Icc (hl i) (hl j)
      ((hproj i).trans (hproj j).symm) (by simp : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
      (Subtype.ext hij)
    have h := congrArg Subtype.val (heq (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1))
    rw [h0 i, h0 j] at h
    exact hy h
  · intro i
    exact ⟨(l i 1).2, hproj i (by simp), by simpa only [mul_one] using hbound i 1 (by simp)⟩

end PoincareConjecture
