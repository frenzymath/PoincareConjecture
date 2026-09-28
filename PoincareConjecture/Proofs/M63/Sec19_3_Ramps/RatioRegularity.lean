import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.Cor19_13_SmoothSlope











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}




theorem m63CurvatureSquared_periodic (F : RicciFlow n M (Icc a b))
    (c : ℝ → ℝ → M) (hc : M62ShrinkingCurve F c) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (m62CurvatureSquared F c t) curvePeriod := by
  have hab : a < b := by
    obtain ⟨s, hs, r, hr, hne⟩ := F.nontrivial
    by_contra! h
    exact hne (by linarith [hs.1, hs.2, hr.1, hr.2])
  have hcont (x : ℝ) : ContinuousOn (fun s => m62CurvatureSquared F c s x) (Icc a b) :=
    (M62.curvatureSquared_continuousOn F c hc).comp
      (continuous_const.prodMk continuous_id).continuousOn (fun _ hs => ⟨mem_univ _, hs⟩)
  intro x
  have hEq : EqOn (fun s => m62CurvatureSquared F c s (x + curvePeriod))
      (fun s => m62CurvatureSquared F c s x) (Ioo a b) :=
    fun s hs => M62.curvatureSquared_periodic F c hc hs x
  exact hEq.of_subset_closure (hcont (x + curvePeriod)) (hcont x)
    Ioo_subset_Icc_self (by rw [closure_Ioo hab.ne]) ht



theorem m63RampRatio_continuousOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c)
    (hu : ∀ t ∈ Icc a b, ∀ x, 0 < m62Slope P c t x) (ε : ℝ) :
    ContinuousOn (fun z : ℝ × ℝ => m63RampRatio P c ε z.2 z.1) (univ ×ˢ Icc a b) := by
  exact (M62.regularized_continuousOn P.flow c hc ε).div
    (m63Slope_continuousOn P c hc) (fun z hz => (hu z.2 hz.2 z.1).ne')




theorem m63RampRatio_contDiffOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c)
    (hu : ∀ t ∈ Icc a b, ∀ x, 0 < m62Slope P c t x) {ε : ℝ} (hε : 0 < ε) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => m63RampRatio P c ε z.2 z.1) (univ ×ˢ Ioo a b) := by
  exact (M62.regularized_smooth P.flow c hε
    (M62.curvatureSquared_contDiffOn P.flow c hc)).div (m63Slope_contDiffOn P c hc)
      (fun z hz => (hu z.2 (Ioo_subset_Icc_self hz.2) z.1).ne')




theorem m63RampRatio_periodic {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) (ε : ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (m63RampRatio P c ε t) curvePeriod := by
  intro x
  simp only [m63RampRatio, m62RegularizedCurvature,
    m63CurvatureSquared_periodic P.flow c hc ht x, m63Slope_periodic P c hc ht x]



theorem m63RampRatio_differentiableAt_time
    {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c)
    (hu : ∀ t ∈ Icc a b, ∀ x, 0 < m62Slope P c t x)
    {ε t : ℝ} (hε : 0 < ε) (ht : t ∈ Ioo a b) (x : ℝ) :
    DifferentiableAt ℝ (fun s => m63RampRatio P c ε s x) t := by
  have h := (m63RampRatio_contDiffOn P c hc hu hε).contDiffAt
    ((isOpen_univ.prod isOpen_Ioo).mem_nhds (show (x, t) ∈ univ ×ˢ Ioo a b from
      ⟨mem_univ _, ht⟩))
  exact (h.comp t (contDiff_const.prodMk contDiff_id).contDiffAt).differentiableAt (by simp)

end PoincareConjecture
