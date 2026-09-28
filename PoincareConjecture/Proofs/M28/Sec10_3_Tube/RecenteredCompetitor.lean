import PoincareConjecture.Proofs.M28.Sec10_3_Tube.IntrinsicSplicing
import PoincareConjecture.Proofs.M28.Sec10_3_Tube.EndpointRecentering

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal Bundle

universe u

namespace PoincareConjecture.M28

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M]

theorem exists_recentered_competitor_of_connectors
    (g : RiemannianMetric 3 M) {U : Set M} {epsilon C A Q : ℝ}
    (hepsilon : 0 < epsilon) (hQ : 0 < Q)
    {γ α β : ℝ → M} {a b : ℝ} {z y : M} (hab : a ≤ b)
    (hγ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 γ (Icc a b))
    (hγU : MapsTo γ (Icc a b) U)
    (hγL : g.pathELength γ a b < ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)))
    (hα0 : α 0 = z) (hα1 : α 1 = γ a)
    (hα : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 α (Icc (0 : ℝ) 1))
    (hαU : MapsTo α (Icc (0 : ℝ) 1) U)
    (hαL : g.pathELength α 0 1 <
      ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ)))
    (hβ0 : β 0 = γ b) (hβ1 : β 1 = y)
    (hβ : ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 β (Icc (0 : ℝ) 1))
    (hβU : MapsTo β (Icc (0 : ℝ) 1) U)
    (hβL : g.pathELength β 0 1 <
      ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ))) :
    ∃ σ : ℝ → M, σ 0 = z ∧ σ 1 = y ∧
      ContMDiffOn 𝓘(ℝ, ℝ) (𝓡 3) 1 σ (Icc (0 : ℝ) 1) ∧
      MapsTo σ (Icc (0 : ℝ) 1) U ∧
      g.pathELength σ 0 1 <
        ENNReal.ofReal ((A + 2 * endpointConnectorBudget epsilon C) *
          Q ^ (-1 / 2 : ℝ)) := by
  obtain ⟨η, hη0, hη1, hη, hηU, hηL⟩ := exists_unit_interval_path g hab hγ hγU
  obtain ⟨τ, hτ0, hτ1, hτ, hτU, hτL⟩ :=
    exists_intrinsic_splice g hα hη hαU hηU (hα1.trans hη0.symm)
  obtain ⟨σ, hσ0, hσ1, hσ, hσU, hσL⟩ :=
    exists_intrinsic_splice g hτ hβ hτU hβU ((hτ1.trans hη1).trans hβ0.symm)
  refine ⟨σ, (hσ0.trans hτ0).trans hα0, hσ1.trans hβ1, hσ, hσU, ?_⟩
  have hsource : 0 < A * Q ^ (-1 / 2 : ℝ) :=
    ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hγL)
  have hconnector : 0 < endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ) :=
    mul_pos (endpointConnectorBudget_pos hepsilon) (Real.rpow_pos_of_pos hQ _)
  rw [hσL, hτL, hηL]
  calc
    g.pathELength α 0 1 + g.pathELength γ a b + g.pathELength β 0 1 <
        ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ)) +
          ENNReal.ofReal (A * Q ^ (-1 / 2 : ℝ)) +
          ENNReal.ofReal (endpointConnectorBudget epsilon C * Q ^ (-1 / 2 : ℝ)) :=
      ENNReal.add_lt_add (ENNReal.add_lt_add hαL hγL) hβL
    _ = ENNReal.ofReal ((A + 2 * endpointConnectorBudget epsilon C) *
        Q ^ (-1 / 2 : ℝ)) := by
      rw [← ENNReal.ofReal_add hconnector.le hsource.le,
        ← ENNReal.ofReal_add (add_nonneg hconnector.le hsource.le) hconnector.le]
      congr 1
      ring

end PoincareConjecture.M28
