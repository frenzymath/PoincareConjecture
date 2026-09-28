import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Soul.Point.Basic
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Ancient.Compact.Diameter.RelativeScalar










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 8

noncomputable section

open Set Filter
open scoped Manifold ContDiff Bundle ENNReal Topology

namespace PoincareConjecture

namespace RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]


theorem coordinateChristoffel_eq_of_inner_eq_mul
    {g h : RiemannianMetric n M} {c : ℝ}
    (hmetric : ∀ x v w, h.inner x v w = c * g.inner x v w)
    (p : M) {x : EuclideanSpace ℝ (Fin n)}
    (hx : x ∈ (extChartAt (𝓡 n) p).target) (v w : EuclideanSpace ℝ (Fin n)) :
    coordinateChristoffel (h.pullbackCoefficients (extChartAt (𝓡 n) p).symm) x v w =
      coordinateChristoffel (g.pullbackCoefficients (extChartAt (𝓡 n) p).symm) x v w := by
  let f := (extChartAt (𝓡 n) p).symm
  let B := g.pullbackCoefficients f
  let H := h.pullbackCoefficients f
  have heq : H = c • B := by
    ext y a b
    exact hmetric _ _ _
  have hD : fderiv ℝ H x = c • fderiv ℝ B x := by
    rw [heq]
    exact congrFun (fderiv_const_smul_field c) x
  have hB := g.isInvertible_chartCoefficients p hx
  have hH := h.isInvertible_chartCoefficients p hx
  apply hH.injective
  change H x ((H x).inverse (metricKoszulCovector (fderiv ℝ H x) v w)) =
    H x ((B x).inverse (metricKoszulCovector (fderiv ℝ B x) v w))
  rw [hH.self_apply_inverse, hD, heq]
  change metricKoszulCovector (c • fderiv ℝ B x) v w =
    c • (B x ((B x).inverse (metricKoszulCovector (fderiv ℝ B x) v w)))
  rw [hB.self_apply_inverse]
  ext z
  simp only [metricKoszulCovector, smul_apply, add_apply, sub_apply,
    ContinuousLinearMap.flip_apply, smul_eq_mul]
  ring


theorem isGeodesicOn_of_inner_eq_mul
    {g h : RiemannianMetric n M} {c : ℝ}
    (hmetric : ∀ x v w, h.inner x v w = c * g.inner x v w)
    {curve : ℝ → M} {s : Set ℝ} (hcurve : h.IsGeodesicOn curve s) :
    g.IsGeodesicOn curve s := by
  intro t ht
  obtain ⟨p, q, w, hqw⟩ := hcurve t ht
  refine ⟨p, q, w, ?_⟩
  filter_upwards [hqw] with u hu
  refine ⟨hu.1, hu.2.1, hu.2.2.1, ?_⟩
  simpa only [coordinateChristoffel_eq_of_inner_eq_mul hmetric p hu.2.1]
    using hu.2.2.2

end RiemannianMetric

namespace CoreNormalization


def positiveRadiusDivide (c : ℝ) (hc : 0 < c) : Ioi (0 : ℝ) ≃ₜ Ioi (0 : ℝ) where
  toFun r := ⟨r.val / c, div_pos r.property hc⟩
  invFun r := ⟨c * r.val, mul_pos hc r.property⟩
  left_inv r := by ext; dsimp; field_simp
  right_inv r := by ext; dsimp; field_simp
  continuous_toFun := (continuous_subtype_val.div_const c).subtype_mk _
  continuous_invFun := (continuous_const.mul continuous_subtype_val).subtype_mk _

end CoreNormalization

namespace AncientKappaNormalization

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]
  [SecondCountableTopology M] [ConnectedSpace M]
  {K : AncientKappaSolution 3 M} {q : M}



def pointSoul (A : AncientKappaNormalization K q 0)
    (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    RiemannianMetric.PointSoulData (A.target.flow.metric 0) where
  center := P.center
  totallyConvex_singleton := by
    intro curve a b hcurve ha hb
    apply P.totallyConvex_singleton curve a b
      (RiemannianMetric.isGeodesicOn_of_inner_eq_mul (c := A.scale) ?_ hcurve) ha hb
    intro x v w
    simpa only [zero_div, zero_add] using A.metric_eq 0 x v w
  euclidean := P.euclidean
  euclidean_zero := P.euclidean_zero
  radial := {
    toHomeomorph := ((Homeomorph.refl _).prodCongr
      (CoreNormalization.positiveRadiusDivide (Real.sqrt A.scale)
        (Real.sqrt_pos.mpr A.scale_pos))).trans P.radial.toHomeomorph
    distance_eq := by
      intro z
      rw [A.toReal_edist_zero]
      simp only [Homeomorph.trans_apply, P.radial.distance_eq]
      change Real.sqrt A.scale * (z.2.val / Real.sqrt A.scale) = z.2.val
      field_simp [(Real.sqrt_pos.mpr A.scale_pos).ne'] }

@[simp] theorem pointSoul_center (A : AncientKappaNormalization K q 0)
    (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    (A.pointSoul P).center = P.center := rfl


theorem pointSoul_distance (A : AncientKappaNormalization K q 0)
    (P : RiemannianMetric.PointSoulData (K.flow.metric 0)) :
    ((A.target.flow.metric 0).edist q (A.pointSoul P).center).toReal =
      Real.sqrt ((K.flow.connection 0).scalarCurvature q) *
        ((K.flow.metric 0).edist q P.center).toReal := by
  rw [pointSoul_center, A.toReal_edist_zero, A.scale_eq]

end AncientKappaNormalization

end PoincareConjecture
