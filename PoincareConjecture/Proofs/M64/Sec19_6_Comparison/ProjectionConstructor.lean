import PoincareConjecture.Definitions.M64Annulus
import PoincareConjecture.Proofs.M15.Prop8_2_CylinderDistance
import PoincareConjecture.Proofs.M64.Sec19_6_Comparison.ProjectionPointwise











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set
open scoped Manifold ContDiff Bundle ENNReal

universe u

namespace PoincareConjecture

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  {a b : ℝ} {F : RicciFlow n M (Set.Icc a b)}
  {circumference : ℝ} (P : M62.CircleProductData F circumference)




theorem m64Projection_edist_le (t : ℝ) (x y : P.charts.Point) :
    (F.metric t).edist x.1 y.1 ≤
      ENNReal.ofReal 1 * (P.flow.metric t).edist x y := by
  let := P.charts.chartedSpace
  let hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) 1
      (Prod.fst : P.charts.Point → M) :=
    (contMDiff_fst.comp P.charts.to_product_smooth).of_le (by simp)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric t).toRiemannianMetric⟩
  apply RiemannianMetric.edist_le_mul_of_tangentNorm_mfderiv_le
    (P.flow.metric t) (F.metric t) hfst (by norm_num)
  intro q v
  rw [← P.charts.split_space]
  unfold RiemannianMetric.tangentNorm
  rw [P.metric_eq]
  simp only [one_mul]
  apply Real.sqrt_le_sqrt
  exact le_add_of_nonneg_right
    ((P.circle.metricOnPoints.toRiemannianMetric.toCore q.2).re_inner_nonneg _)




theorem m64ProjectedAnnulus_of_integrable
    (t : ℝ) (c0 c1 : ℝ → P.charts.Point)
    (A : M64Annulus (P.flow.metric t) c0 c1)
    (harea : IntegrableOn
      (m60AreaDensity (F.metric t) (fun z => (A.map z).1))
      m64AnnulusDomain volume) :
    0 ≤ A.area ∧
      ∃ B : M64Annulus (F.metric t) (fun x => (c0 x).1) (fun x => (c1 x).1),
        B.map = (fun z => (A.map z).1) ∧
        B.area = m64ProjectedAnnulusArea P t A ∧
        0 ≤ B.area ∧ B.area ≤ A.area := by
  let := P.charts.chartedSpace
  let hfst : ContMDiff (𝓡 (n + 1)) (𝓡 n) 1
      (Prod.fst : P.charts.Point → M) :=
    (contMDiff_fst.comp P.charts.to_product_smooth).of_le (by simp)
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 n) : M → Type _) :=
    ⟨(F.metric t).toRiemannianMetric⟩
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 (n + 1)) : P.charts.Point → Type _) :=
    ⟨(P.flow.metric t).toRiemannianMetric⟩
  have hdom : MeasurableSet m64AnnulusDomain := by
    change MeasurableSet {p : LoopPlane |
      0 ≤ p 0 ∧ p 0 ≤ curvePeriod ∧ 0 ≤ p 1 ∧ p 1 ≤ 1}
    measurability
  have hLip : ∀ x y : m64AnnulusDomain,
      (F.metric t).edist ((A.map x).1) ((A.map y).1) ≤
        ENNReal.ofReal A.lipschitz_constant *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by
    intro x y
    calc
      (F.metric t).edist ((A.map x).1) ((A.map y).1) ≤
          ENNReal.ofReal 1 * (P.flow.metric t).edist (A.map x) (A.map y) :=
        m64Projection_edist_le P t (A.map x) (A.map y)
      _ ≤ ENNReal.ofReal 1 *
          (ENNReal.ofReal A.lipschitz_constant *
            ENNReal.ofReal ‖(x : LoopPlane) - y‖) :=
        by simpa using A.lipschitz_on_domain x y
      _ = ENNReal.ofReal A.lipschitz_constant *
          ENNReal.ofReal ‖(x : LoopPlane) - y‖ := by simp
  have hDiff : ∀ᵐ z ∂volume,
      z ∈ m64AnnulusDomain →
        MDifferentiableAt (𝓡 2) (𝓡 n) (fun w => (A.map w).1) z := by
    filter_upwards [A.ae_manifold_differentiable] with z hz
    intro hzdom
    exact (hfst.mdifferentiableAt (by simp)).comp z (hz hzdom)
  have hA_nonneg : 0 ≤ A.area := by
    unfold M64Annulus.area m64AnnulusArea
    exact integral_nonneg (fun _ => m60AreaDensity_nonneg (P.flow.metric t) A.map _)
  let B : M64Annulus (F.metric t) (fun x => (c0 x).1) (fun x => (c1 x).1) :=
    { map := fun z => (A.map z).1
      continuous_on_domain :=
        continuous_fst.continuousOn.comp A.continuous_on_domain
          (fun _ _ => mem_univ _)
      periodic := by
        intro x s
        exact congrArg Prod.fst (A.periodic x s)
      lower_boundary := by
        intro x
        exact congrArg Prod.fst (A.lower_boundary x)
      upper_boundary := by
        intro x
        exact congrArg Prod.fst (A.upper_boundary x)
      lipschitz_constant := A.lipschitz_constant
      lipschitz_nonnegative := A.lipschitz_nonnegative
      lipschitz_on_domain := hLip
      ae_manifold_differentiable := hDiff
      area_integrable := harea }
  have hpoint : ∀ᵐ z ∂volume.restrict m64AnnulusDomain,
      m60AreaDensity (F.metric t) (fun w => (A.map w).1) z ≤
        m60AreaDensity (P.flow.metric t) A.map z := by
    filter_upwards [ae_restrict_mem hdom, ae_restrict_of_ae A.ae_manifold_differentiable]
      with z hzdom hz
    exact m64CircleProduct_projected_density_le P t A.map z (hz hzdom)
  have harea_le : B.area ≤ A.area := by
    change (∫ z in m64AnnulusDomain,
      m60AreaDensity (F.metric t) (fun w => (A.map w).1) z) ≤
      ∫ z in m64AnnulusDomain, m60AreaDensity (P.flow.metric t) A.map z
    exact integral_mono_ae harea A.area_integrable hpoint
  refine ⟨hA_nonneg, ⟨B, rfl, ?_, ?_, harea_le⟩⟩
  · rfl
  · exact integral_nonneg (fun _ => m60AreaDensity_nonneg (F.metric t)
      (fun z => (A.map z).1) _)

end PoincareConjecture
