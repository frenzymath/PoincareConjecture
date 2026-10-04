import PoincareLib.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Construction.AncientLimits.Neck.NeckFourJets

/-!
# Actual metric realizations of the centered four-jet comparison

Morgan--Tian Definition 2.16, printed p. 30, and Claim 11.35,
pp. 289-291. The eligible MetricJets/Realization declaration
`exists_normalizedEuclideanCoefficients_realization` supplies an actual
metric and Levi-Civita connection with the same germ. Its
`exists_normalizedEuclideanCoefficients_curvature_control` supplies the
uniform-threshold pattern. Here the output retains all five full metric
jet differences, ready for a separate scalar-Laplacian continuity theorem.
No time derivative or Laplacian estimate is asserted in this file.
-/

set_option autoImplicit false

open Set Filter
open scoped Manifold ContDiff Topology

universe u

namespace PoincareMT.M32

/-- An actual metric realization retains the full centered four-jet
bound from Definition 2.16, p. 30. Its common constant precedes all neck
and center data used in Claim 11.35, pp. 289-291. -/
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

/-- For every positive four-jet tolerance, one neck accuracy works before
all manifold and center choices. The actual realized metric retains its
exact coefficient germ, giving the spatial input of Definition 2.16,
p. 30, to Claim 11.35, pp. 289-291. -/
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

end PoincareMT.M32
