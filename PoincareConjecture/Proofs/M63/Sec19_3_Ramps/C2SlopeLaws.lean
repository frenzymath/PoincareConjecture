import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.C2SlopeRegularity
import PoincareConjecture.Proofs.M63.Sec19_3_Ramps.RelabelingSlope

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.M63

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b T : ℝ} {F : RicciFlow n M (Icc a b)} {circumference : ℝ}

theorem c2_slope_laws_of_local (P : M62.CircleProductData F circumference)
    (hlocal : M63LocalCurveTheory P.flow) {K0 K1 K2 : ℝ}
    (hBounds : CurveEvolutionAmbientBounds P.flow K0 K1 K2)
    (c : ℝ → ℝ → P.charts.Point)
    (hc : M63C2ShrinkingCurveOn P.flow c (Icc a T)) (hT : a < T) :
    M63C2SlopeLaws P c T K2 := by
  let := P.charts.chartedSpace
  have hTb : T ≤ b := (hc.domain_subset ⟨hT.le, le_rfl⟩).2
  refine ⟨fun _ ht x => c2_abs_slope_le_one P c hc ht x, ?_, ?_⟩
  · intro t ht x
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    have htaus := htaut.trans hts
    have hsub : Icc tau s ⊆ Icc a b := Icc_subset_Icc hatau.le (hsT.le.trans hTb)
    let Q := m63RestrictCircleProduct P tau s hsub htaus
    obtain ⟨phi, d, hphi, _, hpos, _, hd, _, hcd⟩ :=
      hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
        hatau htaus hsT.le (Icc_subset_Icc hatau.le hsT.le)
    have hdM : M62ShrinkingCurve Q.flow d := m63SmoothRestriction hd tau s Subset.rfl htaus
    exact slope_evolution_of_relabeling Q hdM (hphi.differentiable (by norm_num))
      hpos hcd ⟨htaut, hts⟩
  · intro t ht x hu
    obtain ⟨tau, hatau, htaut⟩ := exists_between ht.1
    obtain ⟨s, hts, hsT⟩ := exists_between ht.2
    have htaus := htaut.trans hts
    have hsub : Icc tau s ⊆ Icc a b := Icc_subset_Icc hatau.le (hsT.le.trans hTb)
    let Q := m63RestrictCircleProduct P tau s hsub htaus
    obtain ⟨phi, d, hphi, _, hpos, _, hd, _, hcd⟩ :=
      hlocal.fixed_relabeling T hT hTb (Icc a T) (Or.inl rfl) c hc tau s
        hatau htaus hsT.le (Icc_subset_Icc hatau.le hsT.le)
    have hdM : M62ShrinkingCurve Q.flow d := m63SmoothRestriction hd tau s Subset.rfl htaus
    exact slope_lower_bound_of_relabeling Q hdM (hphi.differentiable (by norm_num))
      hpos hcd (m63RestrictAmbientBounds hBounds tau s hsub htaus) ⟨htaut, hts⟩ hu

end PoincareConjecture.M63
