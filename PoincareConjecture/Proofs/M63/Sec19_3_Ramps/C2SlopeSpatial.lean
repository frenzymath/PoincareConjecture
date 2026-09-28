import PoincareConjecture.Proofs.M63.Sec19_2_CurveEstimates.C2ScalarRegularity
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2SlopeLaws

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem c2_slope_contDiff_of_local (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    {t : ℝ} (ht : t ∈ Ioo a T) : ContDiff ℝ 2 (m62Slope P c t) := by
  let := P.charts.chartedSpace
  have hT : a < T := ht.1.trans ht.2
  have hTb : T ≤ b := (hc.domain_subset ⟨hT.le, le_rfl⟩).2
  obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
  obtain ⟨s, hts, hsT⟩ := exists_between ht.2
  have htaus := htaut.trans hts
  have hsub : Icc tau s ⊆ Icc a b := Icc_subset_Icc hatau.le (hsT.le.trans hTb)
  let Q := m63RestrictCircleProduct P tau s hsub htaus
  obtain ⟨phi, d, hphi, _, hpos, _, hd, _, hcd⟩ :=
    hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
      hatau htaus hsT.le (Icc_subset_Icc hatau.le hsT.le)
  have hdM : M62ShrinkingCurve Q.flow d := m63SmoothRestriction hd tau s Subset.rfl htaus
  have ht' : t ∈ Icc tau s := ⟨htaut.le, hts.le⟩
  have heq : m62Slope P c t = fun x => m62Slope Q d t (phi x) :=
    funext fun _ => slope_eq_of_relabeling Q hdM
      (hphi.differentiable (by norm_num)) hpos ht' (hcd t ht')
  rw [heq]
  have hu : ContDiff ℝ ∞ (m62Slope Q d t) :=
    (m63Slope_contDiffOn Q d hdM).comp_contDiff
      (contDiff_id.prodMk contDiff_const) (fun _ => ⟨mem_univ _, htaut, hts⟩)
  exact (hu.of_le (by decide)).comp hphi

theorem c2_slope_periodic (P : M62.CircleProductData F circumference)
    (c : ℝ → ℝ → P.charts.Point) (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T))
    {t : ℝ} (ht : t ∈ Icc a T) :
    Function.Periodic (m62Slope P c t) curvePeriod := by
  let := P.charts.chartedSpace
  have hv := m63CurveVelocity_periodic
    ((hc.spatial_regular t ht).mdifferentiable (by norm_num)) (hc.periodic t ht)
  intro x
  have hvx : curveVelocity (fun y => c y t) (x + curvePeriod) =
      curveVelocity (fun y => c y t) x := hv x
  have hcx : c (x + curvePeriod) t = c x t := hc.periodic t ht x
  simp only [m62Slope, spatialUnitTangent]
  erw [c2_speed_periodic P.flow c hc ht x, hvx, hcx]

end PoincareConjecture.M63
