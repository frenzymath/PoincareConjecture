import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2SlopeSpatial
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ}

theorem c2_reactionBounds_of_local (F : RicciFlow n M (Icc a b))
    (hlocal : M63LocalCurveTheory F) (c : ℝ → ℝ → M)
    (hc : M63C2ShrinkingCurveOn F c (Icc a T)) (hT : a < T) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    ∃ L : ℝ, ∀ t ∈ Ioo a T, ∀ x,
      -K2 ≤ m62CurvatureSquared F c t x + m62TangentRicci F c t x ∧
        m62CurvatureSquared F c t x + m62TangentRicci F c t x ≤ L := by
  have hcompact : IsCompact (Icc (0 : ℝ) curvePeriod ×ˢ Icc a T) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨Q, hQ⟩ := hcompact.bddAbove_image
    ((c2_curvatureSquared_continuousOn F c hc hT).mono
      (Set.prod_mono (subset_univ _) Subset.rfl))
  refine ⟨Q + K2, fun t ht x => ?_⟩
  have ht' := Ioo_subset_Icc_self ht
  have hS := (c2_unitTangent_norm F c hc ht' x).le
  have hRic := abs_le.mp
    (hBounds.ricci t (hc.domain_subset ht') (c x t) _ _ hS hS)
  change -K2 ≤ m62TangentRicci F c t x ∧ m62TangentRicci F c t x ≤ K2 at hRic
  have hcurvature : m62CurvatureSquared F c t x ≤ Q := by
    obtain ⟨y, hy, hxy⟩ :=
      (c2_curvatureSquared_periodic F c hc hlocal hT ht').exists_mem_Ico₀
        (by unfold curvePeriod; positivity) x
    rw [hxy]
    exact hQ ⟨(y, t), ⟨Ico_subset_Icc_self hy, ht'⟩, rfl⟩
  have hnonneg := M62.curvatureSquared_nonneg F c t x
  constructor <;> linarith

theorem c2_slope_lower {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (hlocal : M63LocalCurveTheory P.flow)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    {m : ℝ} (hm : 0 ≤ m) (hinit : ∀ x, m ≤ m62Slope P c a x) :
    ∀ t ∈ Icc a T, ∀ x,
      m * Real.exp (-K2 * (t - a)) ≤ m62Slope P c t x := by
  let := P.charts.chartedSpace
  obtain ⟨L, hL⟩ := c2_reactionBounds_of_local P.flow hlocal c hc hT hBounds
  have hEq := c2_slope_laws_of_local P hlocal hBounds c hc hT
  have hw (t : ℝ) (ht : t ∈ Ioo a T) :
      ContDiff ℝ 1 (fun x => (curveSpeed P.flow c t x)⁻¹) :=
    ((c2_scalar_contDiff_of_local P.flow c hc hlocal ht).1).inv
      (fun x => (c2_speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne')
  have hu' (t : ℝ) (ht : t ∈ Ioo a T) : ContDiff ℝ 1 (deriv (m62Slope P c t)) :=
    (c2_slope_contDiff_of_local P hlocal c hc ht).deriv'
  have h := Poincare.Parabolic.periodic_exp_le_of_weighted_parabolic_ge
    (F := fun x t => m62Slope P c t x)
    (w := fun x t => (curveSpeed P.flow c t x)⁻¹) (B := fun _ _ => 0)
    (C := fun x t => m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x)
    (p := curvePeriod) (K := K2) (L := L) (m := m)
    (by unfold curvePeriod; positivity) hT hm (c2_slope_continuousOn P c hc hT)
    (fun t ht => c2_slope_periodic P c hc ht)
    (fun x t ht => hEq.evolution t ht x)
    (fun x t ht => (hw t ht).differentiable (by norm_num) x)
    (fun x t ht => (hu' t ht).differentiable (by norm_num) x)
    (fun x t ht => (hL t ht x).1) (fun x t ht => (hL t ht x).2)
    (fun x t _ => by
      simp only [m62ArcSecondDerivative, m62ArcDerivative, zero_mul, add_zero]
      exact le_rfl) hinit
  exact fun t ht x => h x t ht

theorem c2_ramp_preserved {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (hlocal : M63LocalCurveTheory P.flow)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    (hT : a < T) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    ∀ t ∈ Icc a T, M63IsRampAt P (fun x => c x t) t := by
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hcont : Continuous (m62Slope P c a) :=
    (c2_slope_continuousOn P c hc hT).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, le_rfl, hT.le⟩)
  obtain ⟨x0, _, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) curvePeriod).Nonempty from ⟨0, le_rfl, hp.le⟩)
    hcont.continuousOn
  have hm : 0 < m62Slope P c a x0 := (m63IsRampAt_slice_iff P c a).mp hramp x0
  have hinit : ∀ x, m62Slope P c a x0 ≤ m62Slope P c a x := by
    intro x
    obtain ⟨y, hy, hxy⟩ := (c2_slope_periodic P c hc ⟨le_rfl, hT.le⟩).exists_mem_Ico₀ hp x
    rw [hxy]
    exact hmin (Ico_subset_Icc_self hy)
  have hlower := c2_slope_lower P hlocal c hc hT hBounds hm.le hinit
  intro t ht
  rw [m63IsRampAt_slice_iff]
  intro x
  exact (mul_pos hm (Real.exp_pos _)).trans_le (hlower t ht x)

end PoincareConjecture.M63
