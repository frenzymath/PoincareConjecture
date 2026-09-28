import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.SpaceForm.RoundSphere
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Sectional
import PoincareConjecture.Proofs.Horizon.Geometry.Curvature.Hypersurface.Charts
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Construction

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open PoincareConjecture Filter
open scoped ContDiff Manifold Bundle Topology InnerProductSpace

namespace Poincare.Geometry.Riemannian.SpaceForm

private abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

private theorem euclidean_connectionCoefficient {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n)) (x u v : E n) :
    D.connectionCoefficient x u v = 0 := by
  rw [D.connectionCoefficient_eq_coordinateChristoffel]
  change CoordinateExponential.christoffelBilinear
    (RiemannianMetric.euclideanMetric n).euclideanCoefficients x u v = 0
  rw [RiemannianMetric.euclideanMetric_christoffel]
  simp

private theorem euclidean_curvatureTensor {n : ℕ}
    (D : LeviCivitaData (RiemannianMetric.euclideanMetric n))
    (x u v w z : E n) : D.curvatureTensor x u v w z = 0 := by
  have he (a b : E n) : D.euclideanConnection a b = fun _ => 0 := by
    funext y
    exact euclidean_connectionCoefficient D y a b
  unfold LeviCivitaData.curvatureTensor
  rw [D.curvature_eq_euclideanConnection]
  simp only [he, fderiv_const_apply, zero_apply, add_zero,
    sub_self, RiemannianMetric.euclideanMetric_inner, inner_zero_left]

private theorem unit_immersion_normal {m n : ℕ} {F : E m → E n} {x : E m}
    (hF : DifferentiableAt ℝ F x)
    (hunit : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1) (u : E m) :
    inner ℝ (F x) (fderiv ℝ F x u) = 0 := by
  have hd := (hF.hasFDerivAt.inner ℝ hF.hasFDerivAt).fderiv
  have hz : fderiv ℝ (fun y => inner ℝ (F y) (F y)) x = 0 := by
    have heq : (fun y => inner ℝ (F y) (F y)) =ᶠ[𝓝 x] fun _ => 1 := hunit
    rw [heq.fderiv_eq, fderiv_const_apply]
  have he := congrArg (fun L => L u) hd
  rw [hz] at he
  simp only [zero_apply, ContinuousLinearMap.comp_apply, fderivInnerCLM_apply,
    ContinuousLinearMap.prod_apply] at he
  rw [real_inner_comm (F x) (fderiv ℝ F x u)] at he
  linarith

open Poincare.Geometry.Curvature.Hypersurface in

theorem curvatureTensor_of_unit_immersion {m : ℕ}
    {h : RiemannianMetric m (E m)} (D' : LeviCivitaData h)
    {F : E m → E (m + 1)} {x : E m}
    (hF : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ ∞ F y)
    (hunit : ∀ᶠ y in 𝓝 x, inner ℝ (F y) (F y) = 1)
    (hmetric : ∀ᶠ y in 𝓝 x, ∀ a b,
      h.inner y a b = inner ℝ (fderiv ℝ F y a) (fderiv ℝ F y b))
    (u v w z : E m) :
    D'.curvatureTensor x u v w z =
      h.inner x u w * h.inner x v z - h.inner x u z * h.inner x v w := by
  let g := RiemannianMetric.euclideanMetric (m + 1)
  let D := g.euclideanLeviCivitaData
  have hmetric' : ∀ᶠ y in 𝓝 x, ∀ a b,
      h.inner y a b = g.inner (F y) (fderiv ℝ F y a) (fderiv ℝ F y b) := hmetric
  have hNT : ∀ᶠ y in 𝓝 x, ∀ a, g.inner (F y) (F y) (fderiv ℝ F y a) = 0 := by
    filter_upwards [hF, hunit.eventually_nhds] with y hy hUy a
    exact unit_immersion_normal (hy.differentiableAt (by simp)) hUy a
  have hB (a b : E m) :
      g.inner (F x) (secondFundamentalForm D D' F x a b) (F x) = -h.inner x a b := by
    have he := inner_shapeOperator_neg_normal_eq_normal_derivative D D'
      hF.self_of_nhds (hF.self_of_nhds.differentiableAt (by simp)) hNT a b
    rw [inner_shapeOperator] at he
    simp only [covariantDerivativeAlongMap, euclidean_connectionCoefficient,
      add_zero, map_neg, neg_apply] at he
    rw [← hmetric'.self_of_nhds, g.symm (F x) (F x)] at he
    linarith
  have hL := fderiv_injective_of_pullback_metric hmetric'.self_of_nhds
  have hpair (a b c d : E m) :
      g.inner (F x) (secondFundamentalForm D D' F x a b)
        (secondFundamentalForm D D' F x c d) = h.inner x a b * h.inner x c d := by
    rw [metric_inner_normals_eq_mul g (F x) (fderiv ℝ F x).toLinearMap hL
      (F x) hunit.self_of_nhds hNT.self_of_nhds _ _
      (secondFundamentalForm_normal D D' hF.self_of_nhds hmetric' c d)]
    rw [hB, hB, neg_mul_neg]
  rw [gauss_curvatureTensor_of_eventually D D' hF hmetric',
    euclidean_curvatureTensor, zero_add, hpair, hpair]

theorem roundSphereMetric_curvatureTensor {n : ℕ}
    (D : LeviCivitaData (roundSphereMetric n)) (x : UnitSphere n)
    (u v w z : TangentSpace (𝓡 n) x) :
    D.curvatureTensor x u v w z =
      (roundSphereMetric n).inner x u w * (roundSphereMetric n).inner x v z -
        (roundSphereMetric n).inner x u z * (roundSphereMetric n).inner x v w := by
  let : Fact (Module.finrank ℝ (E (n + 1)) = n + 1) := ⟨by simp [E]⟩
  let c := extChartAt (𝓡 n) x
  let y := c x
  let f : UnitSphere n → E (n + 1) := (↑)
  let F : E n → E (n + 1) := f ∘ c.symm
  have hf : ContMDiff (𝓡 n) (𝓡 (n + 1)) ∞ f := contMDiff_coe_sphere
  have hp : c.symm y = x := c.left_inv (mem_extChartAt_source x)
  have hc : ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm y :=
    (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x
      (mem_extChartAt_target x)).contMDiffAt
      (extChartAt_target_mem_nhds' (mem_extChartAt_target x))
  have hcnear : ∀ᶠ a in 𝓝 y, ContMDiffAt (𝓡 n) (𝓡 n) ∞ c.symm a := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with a ha
    exact (contMDiffWithinAt_extChartAt_symm_target (n := ∞) x ha).contMDiffAt
      (extChartAt_target_mem_nhds' ha)
  have hF : ∀ᶠ a in 𝓝 y, ContDiffAt ℝ ∞ F a := by
    filter_upwards [hcnear] with a ha
    exact contMDiffAt_iff_contDiffAt.mp (hf.contMDiffAt.comp a ha)
  have hunit : ∀ᶠ a in 𝓝 y, inner ℝ (F a) (F a) = 1 := by
    apply Filter.Eventually.of_forall
    intro a
    have hnorm : ‖F a‖ = 1 := by
      simpa only [F, Function.comp_apply, f, Metric.mem_sphere, dist_zero_right]
        using (c.symm a).property
    rw [real_inner_self_eq_norm_sq, hnorm, one_pow]
  obtain ⟨gE, DE, hmetric⟩ := LeviCivitaData.exists_chart_metric (roundSphereMetric n) x
  have hmetricF : ∀ᶠ a in 𝓝 y, ∀ b d,
      gE.inner a b d = inner ℝ (fderiv ℝ F a b) (fderiv ℝ F a d) := by
    filter_upwards [hmetric, hcnear] with a hma hca b d
    have hder : fderiv ℝ F a =
        (mfderiv (𝓡 n) (𝓡 (n + 1)) f (c.symm a)).comp
          (mfderiv (𝓡 n) (𝓡 n) c.symm a) := by
      rw [← mfderiv_eq_fderiv]
      exact mfderiv_comp a (hf.contMDiffAt.mdifferentiableAt (by simp))
        (hca.mdifferentiableAt (by simp))
    rw [hma, roundSphereMetric_inner, RiemannianMetric.euclideanMetric_inner, hder]
    rfl
  have hinv : ∀ᶠ a in 𝓝 y, (mfderiv (𝓡 n) (𝓡 n) c.symm a).IsInvertible := by
    filter_upwards [extChartAt_target_mem_nhds' (mem_extChartAt_target x)] with a ha
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm ha
  have hleft (a : TangentSpace (𝓡 n) x) :
      mfderiv (𝓡 n) (𝓡 n) c.symm y (mfderiv (𝓡 n) (𝓡 n) c x a) = a := by
    have hi := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
      (I := 𝓡 n) (mem_extChartAt_source x)
    simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hi
    exact congrArg (fun L => L a) hi
  let L := mfderiv (𝓡 n) (𝓡 n) c x
  have hm (a b : TangentSpace (𝓡 n) x) :
      gE.inner y (L a) (L b) = (roundSphereMetric n).inner x a b := by
    have he := hmetric.self_of_nhds (L a) (L b)
    change gE.inner y (L a) (L b) = (roundSphereMetric n).inner (c.symm y)
      (mfderiv (𝓡 n) (𝓡 n) c.symm y (L a))
      (mfderiv (𝓡 n) (𝓡 n) c.symm y (L b)) at he
    simp only [L, hleft] at he
    erw [hp] at he
    exact he
  have ht := curvatureTensor_of_unit_immersion DE hF hunit hmetricF (L u) (L v) (L w) (L z)
  rw [hm, hm, hm, hm] at ht
  rw [DE.curvatureTensor_eq_pullback_euclidean D hc hinv hmetric] at ht
  simp only [L, hleft] at ht
  erw [hp] at ht
  exact ht

theorem roundSphereMetric_sectionalCurvature {n : ℕ}
    (D : LeviCivitaData (roundSphereMetric n)) (x : UnitSphere n)
    (u v : TangentSpace (𝓡 n) x)
    (huv : (roundSphereMetric n).inner x u u * (roundSphereMetric n).inner x v v -
      ((roundSphereMetric n).inner x u v)^2 ≠ 0) :
    D.sectionalCurvature x u v = 1 := by
  unfold LeviCivitaData.sectionalCurvature
  rw [roundSphereMetric_curvatureTensor,
    (roundSphereMetric n).symm x v u, ← pow_two]
  exact div_self huv

theorem roundSphereMetric_unit_sectionalCurvature {n : ℕ} (x : UnitSphere n)
    (u v : TangentSpace (𝓡 n) x)
    (huv : (roundSphereMetric n).inner x u u * (roundSphereMetric n).inner x v v -
      ((roundSphereMetric n).inner x u v)^2 ≠ 0) :
    (roundSphereMetric n).leviCivitaData.sectionalCurvature x u v = 1 :=
  roundSphereMetric_sectionalCurvature _ x u v huv

end Poincare.Geometry.Riemannian.SpaceForm
