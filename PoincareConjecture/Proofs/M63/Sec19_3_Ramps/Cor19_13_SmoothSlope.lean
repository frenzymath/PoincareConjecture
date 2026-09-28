import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.SlopeRegularity
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicMaximumPrinciple












set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63SmoothReactionBounds (F : RicciFlow n M (Icc a b))
    (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds F K0 K1 K2) :
    ∃ L : ℝ, ∀ t ∈ Ioo a b, ∀ x,
      -K2 ≤ m62CurvatureSquared F c t x + m62TangentRicci F c t x ∧
        m62CurvatureSquared F c t x + m62TangentRicci F c t x ≤ L := by
  have hcompact : IsCompact (Icc (0 : ℝ) curvePeriod ×ˢ Icc a b) :=
    isCompact_Icc.prod isCompact_Icc
  obtain ⟨Q, hQ⟩ := hcompact.bddAbove_image
    ((M62.curvatureSquared_continuousOn F c hc).mono
      (Set.prod_mono (subset_univ _) Subset.rfl))
  refine ⟨Q + K2, fun t ht x => ?_⟩
  have hS := (M62.unitTangent_norm F c hc (Ioo_subset_Icc_self ht) x).le
  have hRic := abs_le.mp
    (hBounds.ricci t (Ioo_subset_Icc_self ht) (c x t) _ _ hS hS)
  change -K2 ≤ m62TangentRicci F c t x ∧ m62TangentRicci F c t x ≤ K2 at hRic
  have hcurvature : m62CurvatureSquared F c t x ≤ Q := by
    obtain ⟨y, hy, hxy⟩ := (M62.curvatureSquared_periodic F c hc ht).exists_mem_Ico₀
      (by unfold curvePeriod; positivity) x
    rw [hxy]
    exact hQ ⟨(y, t), ⟨Ico_subset_Icc_self hy, Ioo_subset_Icc_self ht⟩, rfl⟩
  have hnonneg := M62.curvatureSquared_nonneg F c t x
  constructor <;> linarith



theorem m63SmoothSlope_lower {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    {m : ℝ} (hm : 0 ≤ m) (hinit : ∀ x, m ≤ m62Slope P c a x) :
    ∀ t ∈ Icc a b, ∀ x,
      m * Real.exp (-K2 * (t - a)) ≤ m62Slope P c t x := by
  let := P.charts.chartedSpace
  have hab : a < b := by
    obtain ⟨s, hs, t, ht, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, ht.1, ht.2])
  obtain ⟨L, hL⟩ := m63SmoothReactionBounds P.flow c hc hBounds
  have hw (t : ℝ) (ht : t ∈ Ioo a b) :
      ContDiff ℝ ∞ (fun x => (curveSpeed P.flow c t x)⁻¹) :=
    ((M62.speed_joint_contDiffOn P.flow c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)).inv
        (fun x => (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self ht) x).ne')
  have hu (t : ℝ) (ht : t ∈ Ioo a b) : ContDiff ℝ ∞ (m62Slope P c t) :=
    (m63Slope_contDiffOn P c hc).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, ht⟩)
  have h := Poincare.Parabolic.periodic_exp_le_of_weighted_parabolic_ge
    (F := fun x t => m62Slope P c t x)
    (w := fun x t => (curveSpeed P.flow c t x)⁻¹) (B := fun _ _ => 0)
    (C := fun x t => m62CurvatureSquared P.flow c t x + m62TangentRicci P.flow c t x)
    (p := curvePeriod) (K := K2) (L := L) (m := m)
    (by unfold curvePeriod; positivity) hab hm (m63Slope_continuousOn P c hc)
    (fun t ht => m63Slope_periodic P c hc ht)
    (fun x t ht => M62.hasDerivAt_slope P c hc ht x)
    (fun x t ht => (hw t ht).differentiable (by simp) x)
    (fun x t ht => (contDiff_infty_iff_deriv.mp (hu t ht)).2.differentiable (by simp) x)
    (fun x t ht => (hL t ht x).1) (fun x t ht => (hL t ht x).2)
    (fun x t _ => by
      simp only [m62ArcSecondDerivative, m62ArcDerivative, zero_mul, add_zero]
      exact le_rfl) hinit
  exact fun t ht x => h x t ht




theorem m63SmoothRamp_preserved {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (hramp : M63IsRampAt P (fun x => c x a) a) :
    ∀ t ∈ Icc a b, M63IsRampAt P (fun x => c x t) t := by
  have hab : a ≤ b := by
    obtain ⟨s, hs, _, _, _⟩ := F.nontrivial
    exact hs.1.trans hs.2
  have hp : 0 < curvePeriod := by unfold curvePeriod; positivity
  have hcont : Continuous (m62Slope P c a) :=
    (m63Slope_continuousOn P c hc).comp_continuous
      (continuous_id.prodMk continuous_const) (fun _ => ⟨mem_univ _, le_rfl, hab⟩)
  obtain ⟨x0, _, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) curvePeriod).Nonempty from ⟨0, le_rfl, hp.le⟩)
    hcont.continuousOn
  have hm : 0 < m62Slope P c a x0 := (m63IsRampAt_slice_iff P c a).mp hramp x0
  have hinit : ∀ x, m62Slope P c a x0 ≤ m62Slope P c a x := by
    intro x
    obtain ⟨y, hy, hxy⟩ := (m63Slope_periodic P c hc ⟨le_rfl, hab⟩).exists_mem_Ico₀ hp x
    rw [hxy]
    exact hmin (Ico_subset_Icc_self hy)
  have hlower := m63SmoothSlope_lower P c hc hBounds hm.le hinit
  intro t ht
  rw [m63IsRampAt_slice_iff]
  intro x
  exact (mul_pos hm (Real.exp_pos _)).trans_le (hlower t ht x)

end PoincareConjecture
