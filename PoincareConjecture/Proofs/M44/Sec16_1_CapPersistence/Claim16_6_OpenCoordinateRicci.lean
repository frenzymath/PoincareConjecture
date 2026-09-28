import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Claim16_6_RicciTimeGluing
import PoincareConjecture.Proofs.M07.Geometry.RicciFlow.MetricFamily.Coordinates
import PoincareConjecture.Proofs.M13.CurvatureContractions

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter TopologicalSpace
open scoped Manifold ContDiff Topology BigOperators

namespace PoincareConjecture.M44

local notation "E" n:max => EuclideanSpace ℝ (Fin n)

attribute [local instance] normedAddCommGroupTangentSpaceVectorSpace
  normedSpaceTangentSpaceVectorSpace

theorem open_extChartAt_coe {n : ℕ} (U : Opens (E n)) (x : U) :
    (extChartAt (𝓡 n) x : U → E n) = Subtype.val := by
  ext y
  simp [extChartAt, Opens.chartAt_eq]

theorem open_mfderiv_extChartAt_symm {n : ℕ} (U : Opens (E n)) (q x : U) :
    mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) q).symm (x : E n) =
      ContinuousLinearMap.id ℝ (E n) := by
  have hcharts : extChartAt (𝓡 n) q = extChartAt (𝓡 n) x := by
    unfold extChartAt
    rw [show chartAt (E n) q = chartAt (E n) x by simp [Opens.chartAt_eq]]
  rw [hcharts]
  have hcx := congrFun (open_extChartAt_coe U x) x
  have hd := mfderivWithin_range_extChartAt_symm (I := 𝓡 n) (x := x)
  simp only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at hd
  rw [hcx] at hd
  exact hd

theorem open_pullbackCoefficients_germ {n : ℕ} (U : Opens (E n))
    (g : RiemannianMetric n U) {B : E n → SpacetimeBounds.MetricCoefficient n}
    (hB : ∀ (x : U) (v w : TangentSpace (𝓡 n) x), g.inner x v w = B x v w)
    (x : U) :
    g.pullbackCoefficients (extChartAt (𝓡 n) x).symm =ᶠ[𝓝 (x : E n)] B := by
  filter_upwards [U.isOpen.mem_nhds x.2] with y hy
  let z : U := ⟨y, hy⟩
  have he : (extChartAt (𝓡 n) x).symm y = z := by
    have hcharts : extChartAt (𝓡 n) x = extChartAt (𝓡 n) z := by
      unfold extChartAt
      rw [show chartAt (E n) x = chartAt (E n) z by simp [Opens.chartAt_eq]]
    rw [hcharts]
    have hcz := congrFun (open_extChartAt_coe U z) z
    have hz := extChartAt_to_inv (I := 𝓡 n) z
    rw [hcz] at hz
    exact hz
  ext v w
  change g.inner ((extChartAt (𝓡 n) x).symm y)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y v)
    (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y w) = B y v w
  rw [open_mfderiv_extChartAt_symm U x z]
  change g.inner ((extChartAt (𝓡 n) x).symm y) v w = B y v w
  rw [he]
  exact hB z v w

theorem jetRicci_open_coefficients {n : ℕ} (U : Opens (E n))
    {g : RiemannianMetric n U} (D : LeviCivitaData g)
    {B : E n → SpacetimeBounds.MetricCoefficient n}
    (hB : ∀ (x : U) (v w : TangentSpace (𝓡 n) x), g.inner x v w = B x v w)
    (x : U) (v w : E n) :
    SpacetimeBounds.jetRicci (SpacetimeBounds.metricTwoJet B x) v w =
      D.ricci x v w := by
  have hcx := congrFun (open_extChartAt_coe U x) x
  have hx : (x : E n) ∈ (extChartAt (𝓡 n) x).target := by
    have h := mem_extChartAt_target (I := 𝓡 n) x
    rw [hcx] at h
    exact h
  have hi (y : E n) (hy : y ∈ (extChartAt (𝓡 n) x).target) :
      (mfderiv (𝓡 n) (𝓡 n) (extChartAt (𝓡 n) x).symm y).IsInvertible := by
    simpa only [ModelWithCorners.range_eq_univ, mfderivWithin_univ] using
      isInvertible_mfderivWithin_extChartAt_symm hy
  rw [← SpacetimeBounds.metricTwoJet_congr_of_eventuallyEq
    (open_pullbackCoefficients_germ U g hB x)]
  rw [SpacetimeBounds.jetRicci_metricTwoJet_pullback D (isOpen_extChartAt_target x)
    (contMDiffOn_extChartAt_symm x) hi hx]
  rw [open_mfderiv_extChartAt_symm U x x]
  have he : (extChartAt (𝓡 n) x).symm (x : E n) = x := by
    have h := extChartAt_to_inv (I := 𝓡 n) x
    rw [hcx] at h
    exact h
  change D.ricci ((extChartAt (𝓡 n) x).symm (x : E n)) v w = D.ricci x v w
  rw [he]

theorem ricciFlowOperator_open_coefficients {n : ℕ} (U : Opens (E n))
    {g : RiemannianMetric n U} (D : LeviCivitaData g)
    {B : E n → SpacetimeBounds.MetricCoefficient n}
    (hB : ∀ (x : U) (v w : TangentSpace (𝓡 n) x), g.inner x v w = B x v w)
    (x : U) (v w : E n) :
    SpacetimeBounds.ricciFlowOperator n (SpacetimeBounds.metricTwoJet B x) v w =
      -2 * D.ricci x v w := by
  let R := (show E n →ₗ[ℝ] E n →ₗ[ℝ] ℝ from M13.ricciLinear D x).toContinuousBilinearMap
  have hR := SpacetimeBounds.bilinear_eq_sum_dual (EuclideanSpace.basisFun (Fin n) ℝ)
    ((-2 : ℝ) • R)
  have hop : SpacetimeBounds.ricciFlowOperator n (SpacetimeBounds.metricTwoJet B x) =
      (-2 : ℝ) • R := by
    rw [hR]
    unfold SpacetimeBounds.ricciFlowOperator
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [jetRicci_open_coefficients U D hB]
    rfl
  rw [hop]
  rfl

end PoincareConjecture.M44
