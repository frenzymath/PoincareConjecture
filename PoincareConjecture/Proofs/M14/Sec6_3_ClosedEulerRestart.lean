import PoincareConjecture.Proofs.M14.Mathlib.ClosedODERestart
import PoincareConjecture.Proofs.M14.Sec6_3_ClosedEulerExistence

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M14

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]

theorem exists_closedChartEulerPhase_restart_family {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (s₀ : Icc a b) {z₀ : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
    (hcenter : z₀.1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ c d : ℝ, ∃ s₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ s₁.val = s₀.val ∧ Icc c d ∈ 𝓝[Icc a b] s₀.val ∧
      ∃ γ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
        γ s₀.val = z₀ ∧ ContDiffOn ℝ ∞ γ (Icc c d) ∧
        (∀ s ∈ Icc c d, (γ s).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
          HasDerivWithinAt γ (M08.closedChartEulerPhase F T x₀ (Icc c d) s (γ s))
            (Icc c d) s) ∧
        ∀ᶠ r in 𝓝[Icc c d] s₀.val,
          ∃ V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
            IsOpen V ∧ γ r ∈ V ∧
            ∃ β : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
                EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              ContDiffOn ℝ ∞ β (V ×ˢ Icc c d) ∧ ∀ z ∈ V,
                β (z, r) = z ∧ ∀ s ∈ Icc c d,
                  (β (z, s)).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
                  HasDerivWithinAt (fun t => β (z, t))
                    (M08.closedChartEulerPhase F T x₀ (Icc c d) s (β (z, s)))
                    (Icc c d) s := by
  obtain ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, γ, hinit, hγ, hγdata, hrest⟩ :=
    closedODE_exists_restart_family hab s₀
      ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
      (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
      (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
      ⟨hcenter, mem_univ _⟩
  have hphase {s : ℝ} (hs : s ∈ Icc c d)
      {z : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)}
      (hz : z.1 ∈ (extChartAt (𝓡 n) x₀).target) :=
    closedChartEulerPhase_restrict F hM04 T x₀ htime (Icc_subset_Icc hac hdb) hs hz
  refine ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, γ, hinit, hγ, ?_, ?_⟩
  · intro s hs
    obtain ⟨hmap, hd⟩ := hγdata s hs
    exact ⟨hmap.1, (hphase hs hmap.1).symm ▸ hd⟩
  · filter_upwards [hrest] with r hr
    obtain ⟨V, hV, hγV, β, hβ, hdata⟩ := hr
    refine ⟨V, hV, hγV, β, hβ, ?_⟩
    intro z hz
    refine ⟨(hdata z hz).1, ?_⟩
    intro s hs
    obtain ⟨hmap, hd⟩ := (hdata z hz).2 s hs
    exact ⟨hmap.1, (hphase hs hmap.1).symm ▸ hd⟩

theorem exists_closedChartEulerPhase_restart_along {J : Set ℝ} (F : RicciFlow n M J)
    (hM04 : RicciFlowCurvatureTheory.{u}) (T : ℝ) (x₀ : M)
    {a b : ℝ} (hab : a < b) (htime : ∀ s ∈ Icc a b, T - s ^ 2 ∈ J)
    (s₀ : Icc a b) (γ : ℝ → EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n))
    (hγ : ∀ s ∈ Icc a b, HasDerivWithinAt γ
      (M08.closedChartEulerPhase F T x₀ (Icc a b) s (γ s)) (Icc a b) s)
    (hcenter : (γ s₀.val).1 ∈ (extChartAt (𝓡 n) x₀).target) :
    ∃ c d : ℝ, ∃ s₁ : Icc c d,
      c < d ∧ a ≤ c ∧ d ≤ b ∧ s₁.val = s₀.val ∧ Icc c d ∈ 𝓝[Icc a b] s₀.val ∧
        ∀ᶠ r in 𝓝[Icc c d] s₀.val,
          ∃ V : Set (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)),
            IsOpen V ∧ γ r ∈ V ∧
            ∃ β : (EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n)) × ℝ →
                EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n),
              ContDiffOn ℝ ∞ β (V ×ˢ Icc c d) ∧ ∀ z ∈ V,
                β (z, r) = z ∧ ∀ s ∈ Icc c d,
                  (β (z, s)).1 ∈ (extChartAt (𝓡 n) x₀).target ∧
                  HasDerivWithinAt (fun t => β (z, t))
                    (M08.closedChartEulerPhase F T x₀ (Icc c d) s (β (z, s)))
                    (Icc c d) s := by
  obtain ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, hrest⟩ :=
    closedODE_exists_restart_along hab s₀
      ((isOpen_extChartAt_target (I := 𝓡 n) x₀).prod isOpen_univ)
      (Function.uncurry (M08.closedChartEulerPhase F T x₀ (Icc a b)))
      (M08.closedChartEulerPhase_contDiffOn F hM04 T x₀ (uniqueDiffOn_Icc hab) htime)
      γ hγ ⟨hcenter, mem_univ _⟩
  refine ⟨c, d, s₁, hcd, hac, hdb, hi, hnear, ?_⟩
  filter_upwards [hrest] with r hr
  obtain ⟨V, hV, hγV, β, hβ, hdata⟩ := hr
  refine ⟨V, hV, hγV, β, hβ, ?_⟩
  intro z hz
  refine ⟨(hdata z hz).1, ?_⟩
  intro s hs
  obtain ⟨hmap, hd⟩ := (hdata z hz).2 s hs
  refine ⟨hmap.1, ?_⟩
  rw [closedChartEulerPhase_restrict F hM04 T x₀ htime (Icc_subset_Icc hac hdb) hs hmap.1]
  exact hd

end PoincareConjecture.M14
