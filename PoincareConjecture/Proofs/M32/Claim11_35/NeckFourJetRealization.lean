import PoincareConjecture.Proofs.M32.Claim11_35.NeckFourJets














set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareConjecture.M32




theorem exists_normalizedEuclideanCoefficients_realization_fourJet_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {M : Type u} [TopologicalSpace M]
      [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
      [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
      {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ 1 / 4 →
      ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
      ∃ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_D : LeviCivitaData h),
        (h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) ∧
        ∀ r : ℕ, r ≤ 4 →
          ‖iteratedFDeriv ℝ r h.euclideanCoefficients 0 -
            iteratedFDeriv ℝ r roundCylinderEuclideanMetric.euclideanCoefficients 0‖ ≤
              C * N.epsilon := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedEuclideanCoefficients_fourJet_bound.{u}
  refine ⟨C, hC, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs
  obtain ⟨h, D, heq⟩ := N.exists_normalizedEuclideanCoefficients_realization q hs
  refine ⟨h, D, heq, ?_⟩
  intro r hr
  have hmodel : roundCylinderEuclideanMetric.euclideanCoefficients =
      roundCylinderEuclideanCoefficients := by
    funext x
    ext v w
    rfl
  have herr : (fun x => h.euclideanCoefficients x -
      roundCylinderEuclideanMetric.euclideanCoefficients x) =ᶠ[𝓝 0]
      (fun x => N.normalizedEuclideanCoefficients q s x -
        roundCylinderEuclideanCoefficients x) := by
    filter_upwards [heq] with x hx
    rw [hx, hmodel]
  rw [← iteratedFDeriv_sub_apply
    ((h.contDiffAt_euclideanCoefficients 0).of_le (by exact_mod_cast le_top))
    ((roundCylinderEuclideanMetric.contDiffAt_euclideanCoefficients 0).of_le
      (by exact_mod_cast le_top))]
  exact ((herr.iteratedFDeriv ℝ r).self_of_nhds ▸ hbound N hε q hs r hr)





theorem exists_normalizedEuclideanCoefficients_realization_fourJet_control
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 / 200 ∧
      ∀ {M : Type u} [TopologicalSpace M]
        [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
        [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
        {g : RiemannianMetric 3 M}, ∀ (N : EpsilonNeck g), N.epsilon ≤ ε₀ →
        ∀ (q : UnitTwoSphere) {s : ℝ}, s ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ →
        ∃ (h : RiemannianMetric 3 (EuclideanSpace ℝ (Fin 3))) (_D : LeviCivitaData h),
          (h.euclideanCoefficients =ᶠ[𝓝 0] N.normalizedEuclideanCoefficients q s) ∧
          ∀ r : ℕ, r ≤ 4 →
            ‖iteratedFDeriv ℝ r h.euclideanCoefficients 0 -
              iteratedFDeriv ℝ r roundCylinderEuclideanMetric.euclideanCoefficients 0‖ < δ := by
  obtain ⟨C, hC, hbound⟩ := exists_normalizedEuclideanCoefficients_realization_fourJet_bound.{u}
  refine ⟨min (1 / 200) (δ / (2 * C)), lt_min (by norm_num) (by positivity),
    min_le_left _ _, ?_⟩
  intro M _ _ _ _ _ _ _ g N hε q s hs
  have hquarter : N.epsilon ≤ 1 / 4 :=
    (hε.trans (min_le_left _ _)).trans (by norm_num)
  obtain ⟨h, D, heq, hjets⟩ := hbound N hquarter q hs
  refine ⟨h, D, heq, fun r hr => (hjets r hr).trans_lt ?_⟩
  have hh := (le_div_iff₀ (show 0 < 2 * C by positivity)).mp
    (hε.trans (min_le_right _ _))
  nlinarith

end PoincareConjecture.M32
