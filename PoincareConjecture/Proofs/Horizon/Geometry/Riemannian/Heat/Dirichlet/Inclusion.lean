import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Heat.Dirichlet.Resolvent









set_option autoImplicit false

noncomputable section

open Set MeasureTheory UniformSpace
open scoped Manifold ContDiff InnerProductSpace

namespace PoincareConjecture.LeviCivitaData.Dirichlet

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [MeasurableSpace M] [BorelSpace M] [T3Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {g : RiemannianMetric n M} {D : LeviCivitaData g} {Ω₁ Ω₂ : Set M}


def testInclusion (hΩ : Ω₁ ⊆ Ω₂) : EnergyTest D Ω₁ →ₗᵢ[ℝ] EnergyTest D Ω₂ where
  toFun f := ⟨f, f.smooth, f.hasCompactSupport, f.support_subset.trans hΩ⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  norm_map' _ := rfl

@[simp] theorem testInclusion_apply (hΩ : Ω₁ ⊆ Ω₂) (f : EnergyTest D Ω₁) (x : M) :
    testInclusion hΩ f x = f x := rfl


def inclusion (hΩ : Ω₁ ⊆ Ω₂) : H1Zero D Ω₁ →L[ℝ] H1Zero D Ω₂ :=
  Poincare.Analysis.Dirichlet.completionMap
    (Completion.toComplL.comp (testInclusion (D := D) hΩ).toContinuousLinearMap)

@[simp] theorem inclusion_coe (hΩ : Ω₁ ⊆ Ω₂) (f : EnergyTest D Ω₁) :
    inclusion hΩ (f : H1Zero D Ω₁) = (testInclusion hΩ f : H1Zero D Ω₂) :=
  Poincare.Analysis.Dirichlet.completionMap_coe _ _

@[simp] theorem norm_inclusion (hΩ : Ω₁ ⊆ Ω₂) (u : H1Zero D Ω₁) :
    ‖inclusion hΩ u‖ = ‖u‖ := by
  induction u using Completion.induction_on with
  | hp => exact isClosed_eq (inclusion hΩ).continuous.norm continuous_norm
  | ih f => simp


def inclusionIsometry (hΩ : Ω₁ ⊆ Ω₂) : H1Zero D Ω₁ →ₗᵢ[ℝ] H1Zero D Ω₂ where
  toLinearMap := (inclusion hΩ).toLinearMap
  norm_map' := norm_inclusion hΩ

@[simp] theorem inner_inclusion (hΩ : Ω₁ ⊆ Ω₂) (u v : H1Zero D Ω₁) :
    ⟪inclusion hΩ u, inclusion hΩ v⟫_ℝ = ⟪u, v⟫_ℝ :=
  (inclusionIsometry hΩ).inner_map_map u v

@[simp] theorem testToL2_testInclusion (hΩ : Ω₁ ⊆ Ω₂) (f : EnergyTest D Ω₁) :
    testToL2 D Ω₂ (testInclusion hΩ f) = testToL2 D Ω₁ f := rfl

@[simp] theorem toL2_inclusion (hΩ : Ω₁ ⊆ Ω₂) (u : H1Zero D Ω₁) :
    toL2 D Ω₂ (inclusion hΩ u) = toL2 D Ω₁ u := by
  induction u using Completion.induction_on with
  | hp =>
    exact isClosed_eq ((toL2 D Ω₂).continuous.comp (inclusion hΩ).continuous)
      (toL2 D Ω₁).continuous
  | ih f => simp

theorem resolvent_inner_inclusion (hΩ : Ω₁ ⊆ Ω₂)
    (f : Lp ℝ 2 g.volumeMeasure) (v : H1Zero D Ω₁) :
    ⟪resolvent D Ω₂ f, inclusion hΩ v⟫_ℝ = ⟪resolvent D Ω₁ f, v⟫_ℝ := by
  rw [resolvent_inner, toL2_inclusion, resolvent_inner]


theorem l2Resolvent_quadratic_mono (hΩ : Ω₁ ⊆ Ω₂) (f : Lp ℝ 2 g.volumeMeasure) :
    ⟪l2Resolvent D Ω₁ f, f⟫_ℝ ≤ ⟪l2Resolvent D Ω₂ f, f⟫_ℝ := by
  have h := real_inner_self_nonneg (x :=
    resolvent D Ω₂ f - inclusion hΩ (resolvent D Ω₁ f))
  rw [inner_sub_left, inner_sub_right, inner_sub_right, inner_inclusion,
    resolvent_inner_inclusion] at h
  have hsymm : ⟪inclusion hΩ (resolvent D Ω₁ f), resolvent D Ω₂ f⟫_ℝ =
      ⟪resolvent D Ω₂ f, inclusion hΩ (resolvent D Ω₁ f)⟫_ℝ := real_inner_comm _ _
  rw [hsymm, resolvent_inner_inclusion] at h
  rw [l2Resolvent_inner, l2Resolvent_inner]
  linarith

end PoincareConjecture.LeviCivitaData.Dirichlet
