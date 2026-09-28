import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Laplacian











noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.EpsilonNeck



theorem exists_scalar_evolution_margin :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M] {g : RiemannianMetric 3 M},
      ∀ (N : EpsilonNeck g) (D : LeviCivitaData g), N.epsilon ≤ ε₀ →
        (1 / 2 : ℝ) * D.scalarCurvature N.center ^ 2 ≤
          D.laplacian D.scalarCurvature N.center + 2 * D.ricciNormSq N.center := by
  obtain ⟨ε₀, hε₀, hsmall, hcontrol⟩ :=
    exists_normalized_scalar_laplacian_control.{u} (α := 1 / 6) (by norm_num)
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ g N D hε
  have hcenter := N.center_on_central_sphere
  rw [N.central_sphere_eq] at hcenter
  obtain ⟨⟨q, s⟩, ⟨_, hs⟩, hcenter⟩ := hcenter
  have hs0 : s = 0 := Set.mem_singleton_iff.mp hs
  subst s
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  obtain ⟨h, Dh, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hzero
  exact N.scalar_evolution_margin_of_normalized_laplacian D q hcenter Dh heq
    (abs_lt.mp (hcontrol N hε q hzero Dh heq)).1.le

end PoincareConjecture.EpsilonNeck

namespace PoincareConjecture.RicciFlow



theorem exists_neck_scalar_time_derivative_margin
    (hM04 : RicciFlowCurvatureTheory.{u}) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
        [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
        [T2Space M] [T3Space M],
      ∀ {J : Set ℝ} (F : RicciFlow 3 M J) {t : ℝ}, t ∈ J →
      ∀ (N : EpsilonNeck (F.metric t)), N.epsilon ≤ ε₀ →
        ∃ d : ℝ,
          HasDerivWithinAt (fun s => (F.connection s).scalarCurvature N.center) d J t ∧
          (1 / 2 : ℝ) * (F.connection t).scalarCurvature N.center ^ 2 ≤ d := by
  obtain ⟨ε₀, hε₀, hsmall, hmargin⟩ := EpsilonNeck.exists_scalar_evolution_margin.{u}
  refine ⟨ε₀, hε₀, hsmall, ?_⟩
  intro M _ _ _ _ _ _ _ J F t ht N hε
  exact ⟨_, hM04.scalar_evolution 3 M J F t ht N.center,
    hmargin N (F.connection t) hε⟩

end PoincareConjecture.RicciFlow
