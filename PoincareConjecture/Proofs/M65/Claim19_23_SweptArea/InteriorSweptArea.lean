import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.SweptDensity
import PoincareConjecture.Proofs.M65.Claim19_23_SweptArea.RectangleIntegral
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity









set_option autoImplicit false

open MeasureTheory
open scoped Manifold ContDiff Bundle intervalIntegral

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}




theorem m65InteriorSweptAnnulus_area_le {K0 K1 K2 : ℝ}
    (bounds : CurveEvolutionAmbientBounds F K0 K1 K2) (hK2 : 0 ≤ K2)
    {c : ℝ → ℝ → M} (hc : M62ShrinkingCurve F c)
    {s t q : ℝ} (has : a < s) (hst : s ≤ t) (htb : t < b)
    (hq : q ∈ Set.Icc a b) :
    (m65InteriorSweptAnnulus (F.metric q) hc has hst htb).area ≤
      Real.exp ((2 * K2) * (b - a)) * ∫ r in s..t, m62TotalCurvature F c r := by
  let tau : ℝ → ℝ := fun y => s + (t - s) * Real.smoothTransition y
  let factor := Real.exp ((2 * K2) * (b - a))
  let density : LoopPlane → ℝ := fun p => factor *
    (((t - s) * deriv Real.smoothTransition (p 1)) *
      (m62Curvature F c (tau (p 1)) (p 0) * curveSpeed F c (tau (p 1)) (p 0)))
  have htau (y : ℝ) : tau y ∈ Set.Icc a b :=
    ⟨has.le.trans (m65SweptTime_mem hst y).1, (m65SweptTime_mem hst y).2.trans htb.le⟩
  have hdata : Continuous (fun p : LoopPlane =>
      m62Curvature F c (tau (p 1)) (p 0) * curveSpeed F c (tau (p 1)) (p 0)) :=
    ((M62.curvature_continuousOn F c hc).mul (M62.speed_continuousOn F c hc)).comp_continuous
      (f := fun p : LoopPlane => (p 0, tau (p 1))) (by dsimp [tau]; fun_prop)
      (fun p => ⟨Set.mem_univ _, htau (p 1)⟩)
  have hderiv : Continuous (deriv Real.smoothTransition) :=
    (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)
  have hdensity : Continuous density := continuous_const.mul
    ((continuous_const.mul (hderiv.comp (by fun_prop : Continuous (fun p : LoopPlane => p 1)))).mul
      hdata)
  have hbound : (m65InteriorSweptAnnulus (F.metric q) hc has hst htb).area ≤
      ∫ p in m64AnnulusDomain, density p := by
    apply setIntegral_mono_on
      (m65InteriorSweptAnnulus (F.metric q) hc has hst htb).area_integrable
      (hdensity.continuousOn.integrableOn_compact m65AnnulusDomain_isCompact)
      m65AnnulusDomain_isCompact.isClosed.measurableSet
    intro p _
    have hp : annulusPoint (p 0) (p 1) = p := by
      ext i
      fin_cases i <;> rfl
    have h := m65SweptDensity_fixedMetric_le bounds hK2 hc has hst htb hq (p 0) (p 1)
    rw [hp] at h
    simpa only [m65InteriorSweptAnnulus_map, density, factor, tau, mul_assoc] using h
  have hinner (y : ℝ) :
      (∫ x in (0 : ℝ)..curvePeriod, density (annulusPoint x y)) =
        factor * (((t - s) * deriv Real.smoothTransition y) * m62TotalCurvature F c (tau y)) := by
    change (∫ x in (0 : ℝ)..curvePeriod, factor *
      (((t - s) * deriv Real.smoothTransition y) *
        (m62Curvature F c (tau y) x * curveSpeed F c (tau y) x))) = _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    rfl
  have hint : (∫ p in m64AnnulusDomain, density p) =
      factor * ∫ r in s..t, m62TotalCurvature F c r := by
    rw [m65Integral_annulusDomain hdensity]
    simp_rw [hinner]
    rw [intervalIntegral.integral_const_mul]
    congr 1
    exact Real.integral_affine_smoothTransition hst
      ((M62.total_curvature_continuous F c hc).mono
        (fun _ hr => ⟨has.le.trans hr.1, hr.2.trans htb.le⟩))
  exact hbound.trans_eq hint

end PoincareConjecture
