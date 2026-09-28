import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2RatioRegularity











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}



theorem ramp_immersed (P : M62.CircleProductData F circumference)
    {gamma : ℝ → P.charts.Point} {t : ℝ} (hramp : M63IsRampAt P gamma t) :
    ∀ x, curveVelocity (n := n + 1) gamma x ≠ 0 := by
  intro x hx
  simpa [m62Slope, spatialUnitTangent, hx] using hramp x





theorem c2_initial_ramp_bounds (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    ∃ m R0 : ℝ, 0 < m ∧ 0 ≤ R0 ∧ (∀ x, m ≤ m62Slope P c a x) ∧
      ∀ x, m63RampRatio P c 1 a x ≤ R0 := by
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  have ha : a ∈ Icc a T := ⟨le_rfl, hT.le⟩
  have hu : ∀ x, 0 < m62Slope P c a x := (m63IsRampAt_slice_iff P c a).mp hramp
  have hcont : Continuous (m62Slope P c a) :=
    (c2_slope_continuousOn P c hc hT).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ha⟩)
  have hnum : Continuous (m62RegularizedCurvature P.flow c 1 a) :=
    (c2_regularized_continuousOn P.flow c hc hT 1).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, ha⟩)
  have hratio : Continuous (m63RampRatio P c 1 a) :=
    hnum.div hcont (fun x => (hu x).ne')
  obtain ⟨x0, _, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) curvePeriod).Nonempty from ⟨0, le_rfl, hp.le⟩)
    hcont.continuousOn
  obtain ⟨R, hR⟩ := isCompact_Icc.bddAbove_image
    (hratio.continuousOn : ContinuousOn _ (Icc (0 : ℝ) curvePeriod))
  refine ⟨m62Slope P c a x0, max 0 R, hu x0, le_max_left _ _, ?_, ?_⟩
  · intro x
    obtain ⟨y, hy, hxy⟩ := (c2_slope_periodic P c hc ha).exists_mem_Ico₀ hp x
    rw [hxy]
    exact hmin (Ico_subset_Icc_self hy)
  · intro x
    obtain ⟨y, hy, hxy⟩ :=
      (c2_rampRatio_periodic P hlocal c hc hT 1 ha).exists_mem_Ico₀ hp x
    rw [hxy]
    exact (hR ⟨y, Ico_subset_Icc_self hy, rfl⟩).trans (le_max_right _ _)

end PoincareConjecture.M63
