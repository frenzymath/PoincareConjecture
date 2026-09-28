import PoincareConjecture.Proofs.M14.Mathlib.ClosedODEPathFamily
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerExistence

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Metric Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_closedChartEulerPhase_smooth_path_family {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (s₀ : Icc a b)
    {z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hz₀ : z₀.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ c d : ℝ, ∃ s₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ s₁.val = s₀.val ∧ Icc c d ∈ 𝓝[Icc a b] s₀.val ∧
      ∃ ρ > (0 : ℝ),
      ∃ Φ : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) →
          C(Icc c d, EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ Φ (ball z₀ ρ) ∧ ∀ z ∈ ball z₀ ρ,
          Φ z s₁ = z ∧ (∀ s : Icc c d, (Φ z s).1 ∈ (extChartAt (𝓡 n) x₀).target) ∧
          ContDiffOn ℝ ∞
            (fun s => Φ z (projIcc c d (s₁.property.1.trans s₁.property.2) s)) (Icc c d) ∧
          ∀ s : Icc c d, HasDerivWithinAt
            (fun r => Φ z (projIcc c d (s₁.property.1.trans s₁.property.2) r))
            (M08.closedChartEulerPhase F T x₀ (Icc c d) s.val (Φ z s)) (Icc c d) s.val := by
  obtain ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, ρ, hρ, Φ, hΦ, hdata⟩ :=
    closedODE_exists_smooth_path_family hab s₀
      ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
      (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
      (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
      ⟨hz₀, mem_univ _⟩
  refine ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, ρ, hρ, Φ, hΦ, ?_⟩
  intro z hz
  obtain ⟨hz₁, hmap, hsm, hd⟩ := hdata z hz
  refine ⟨hz₁, fun s => (hmap s).1, hsm, ?_⟩
  intro s
  rw [closedChartEulerPhase_restrict F hM04 T x₀ htime (Icc_subset_Icc hac hdb)
    s.property (hmap s).1]
  exact hd s

end PoincareConjecture.M14
