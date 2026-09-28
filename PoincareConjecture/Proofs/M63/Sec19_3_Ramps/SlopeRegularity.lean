import PoincareConjecture.Proofs.M62.Claim19_11_SlopeLaws
import PoincareConjecture.Proofs.M62.Lemma0_4_Continuity
import PoincareConjecture.Proofs.M62.Lemma0_4_Periodicity
import PoincareConjecture.Statements.M63CurveEstimates

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ}

omit [IsManifold (𝓡 n) ∞ M] in

theorem m63CurveVelocity_periodic {gamma : ℝ → M} {p : ℝ}
    (hgamma : MDifferentiable 𝓘(ℝ, ℝ) (𝓡 n) gamma)
    (hper : Function.Periodic gamma p) :
    Function.Periodic (fun x => (curveVelocity gamma x : EuclideanSpace ℝ (Fin n))) p := by
  intro x
  have hshift : HasDerivAt (fun y : ℝ => y + p) 1 x := (hasDerivAt_id x).add_const p
  have hvalue : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => y + p) x 1 = 1 := by
    rw [mfderiv_eq_fderiv, hshift.hasFDerivAt.fderiv]
    exact ContinuousLinearMap.toSpanSingleton_apply_one ℝ 1
  have hcomp := congrArg (fun L : ℝ →L[ℝ] EuclideanSpace ℝ (Fin n) => L 1)
    (mfderiv_comp (f := fun y : ℝ => y + p) (g := gamma) x (hgamma (x + p))
      hshift.hasFDerivAt.hasMFDerivAt.mdifferentiableAt)
  change mfderiv 𝓘(ℝ, ℝ) (𝓡 n) (fun y => gamma (y + p)) x 1 =
    mfderiv 𝓘(ℝ, ℝ) (𝓡 n) gamma (x + p)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun y : ℝ => y + p) x 1) at hcomp
  rw [hvalue, funext hper] at hcomp
  exact hcomp.symm

theorem m63Slope_continuousOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) :
    ContinuousOn (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Icc a b) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.continuous.continuousOn.comp
    hc.continuous (fun _ _ => mem_univ _)
  have hpair := M62.metric_pairing_continuousOn P.flow c hc.continuous _ _
    hc.velocity_continuous hB
  have hinv := (M62.speed_continuousOn P.flow c hc).inv₀
    (fun z hz => (M62.speed_pos P.flow c hc hz.2 z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul]
    using hinv.mul hpair

theorem m63Slope_contDiffOn {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) :
    ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => m62Slope P c z.2 z.1) (univ ×ˢ Ioo a b) := by
  let := P.charts.chartedSpace
  have hB := (M62.circleProduct_identities P).circle_unit_smooth.comp_contMDiffOn
    hc.joint_smooth
  have hpair := M62.metric_pairing_contDiffOn P.flow c hc.joint_smooth _ _
    (M62.spatial_velocity_joint_contMDiff P.flow c hc) hB
  have hinv := (M62.speed_joint_contDiffOn P.flow c hc).inv
    (fun z hz => (M62.speed_pos P.flow c hc (Ioo_subset_Icc_self hz.2) z.1).ne')
  simpa only [Pi.mul_def, Pi.inv_def, m62Slope, spatialUnitTangent,
    map_smul, smul_apply, smul_eq_mul]
    using hinv.mul hpair

theorem m63Slope_periodic {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point)
    (hc : M62ShrinkingCurve P.flow c) {t : ℝ} (ht : t ∈ Icc a b) :
    Function.Periodic (m62Slope P c t) curvePeriod := by
  let := P.charts.chartedSpace
  have hv := m63CurveVelocity_periodic
    (fun x => (hc.spatial_regular t ht x).mdifferentiableAt (by norm_num))
    (hc.periodic t ht)
  intro x
  have hvx : curveVelocity (fun y => c y t) (x + curvePeriod) =
      curveVelocity (fun y => c y t) x := hv x
  simp only [m62Slope, spatialUnitTangent]
  rw [M62.speed_periodic P.flow c hc ht x, hvx, hc.periodic t ht x]

theorem m63IsRampAt_slice_iff {F : RicciFlow n M (Icc a b)} {circumference : ℝ}
    (P : M62.CircleProductData F circumference) (c : ℝ → ℝ → P.charts.Point) (t : ℝ) :
    M63IsRampAt P (fun x => c x t) t ↔ ∀ x, 0 < m62Slope P c t x := by
  rfl

end PoincareConjecture
