import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.SourceNames.LGeometry
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Calculus.ODE.Families.ClosedODEJointFamily
import PoincareLib.Geometry.RicciFlow.Generalized.ReducedGeometry.Exponential.Families.ClosedEulerExistence

/-!
# Jointly smooth local families of actual closed Euler phases

Morgan-Tian Lemma 6.18, pp. 113-114. M08's actual phase field satisfies
the closed ODE hypotheses. The resulting local family is jointly smooth
in the initial phase and closed time, and genuine spatial derivatives
identify the actual phase coefficients on the retained interval.
-/

set_option autoImplicit false
-- The actual phase coefficients use the standard Euclidean tangent models.
set_option backward.isDefEq.respectTransparency false

open Set Filter Metric
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

/-- The actual closed Euler phase has a jointly smooth local family
through every nearby initial phase. It remains in the chart and solves
the actual within equation on its own closed interval, including both
endpoints, Lemma 6.18, pp. 113-114. -/
theorem exists_closedChartEulerPhase_joint_family {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (s₀ : Icc a b)
    {z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hz₀ : z₀.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ c d : ℝ, ∃ s₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ s₁.val = s₀.val ∧ Icc c d ∈ 𝓝[Icc a b] s₀.val ∧
      ∃ ρ > (0 : ℝ),
      ∃ α : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
          EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        ContDiffOn ℝ ∞ α (ball z₀ ρ ×ˢ Icc c d) ∧ ∀ z ∈ ball z₀ ρ,
          α (z, s₁.val) = z ∧ ∀ s ∈ Icc c d,
            (α (z, s)).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
            HasDerivWithinAt (fun r => α (z, r))
              (M08.closedChartEulerPhase F T x₀ (Icc c d) s (α (z, s))) (Icc c d) s := by
  obtain ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, ρ, hρ, α, hα, hdata⟩ :=
    closedODE_exists_joint_family hab s₀
      ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
      (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
      (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
      ⟨hz₀, mem_univ _⟩
  refine ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, ρ, hρ, α, hα, ?_⟩
  intro z hz
  refine ⟨(hdata z hz).1, ?_⟩
  intro s hs
  obtain ⟨hmap, hd⟩ := (hdata z hz).2 s hs
  refine ⟨hmap.1, ?_⟩
  rw [closedChartEulerPhase_restrict F hM04 T x₀ htime (Icc_subset_Icc hac hdb) hs hmap.1]
  exact hd

end PoincareMT.M14
