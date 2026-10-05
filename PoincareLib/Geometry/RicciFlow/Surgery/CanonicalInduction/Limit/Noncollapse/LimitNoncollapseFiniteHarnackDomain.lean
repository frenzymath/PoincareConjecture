import PoincareLib.Geometry.RicciFlow.Blowup.Controlled.Data
import PoincareLib.Geometry.RicciFlow.Harnack.Regularity
import PoincareLib.Geometry.RicciFlow.Harnack.Noncompact.CurvatureControl
import PoincareLib.Geometry.Riemannian.Curvature.Scalar.SharpBounds
import PoincareLib.Geometry.Curvature.Operator.RicciBounds

/-!
# The actual finite backward domain and its slice bounds

The left endpoint stays excluded. Restriction preserves the selected metric
and connection, and singleton compactness supplies separate operator bounds.
Source: MT Proposition 17.1; reviewed limit-tail-finite-harnack-distance F1.
-/

set_option autoImplicit false

open Set
open scoped Manifold ContDiff ENNReal

universe u

namespace PoincareMT.M47

private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    TopologicalSpace L.carrier.carrier := L.carrier.topologicalSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) L.carrier.carrier := L.carrier.chartedSpace
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    IsManifold (𝓡 3) ∞ L.carrier.carrier := L.carrier.isManifold
private local instance {J : Set ℝ} (L : BlowupLimitFlow.{u} J) :
    T3Space L.carrier.carrier := L.carrier.t3Space

/-- A positive finite backward horizon is the literal left-open interval. -/
theorem limitFinite_domain_eq {H : ℝ≥0∞} (hfinite : H ≠ ⊤) :
    blowupBackwardInterval H = Ioc (-H.toReal) 0 := by
  ext t
  constructor
  · rintro ⟨ht, hH⟩
    have h := (ENNReal.ofReal_lt_iff_lt_toReal (neg_nonneg.mpr ht) hfinite).mp hH
    exact ⟨by linarith, ht⟩
  · rintro ⟨hH, ht⟩
    exact ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal (neg_nonneg.mpr ht) hfinite).mpr
      (by linarith)⟩

/-- The finite horizon has strictly positive real length. -/
theorem limitFinite_horizon_pos {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤) :
    0 < H.toReal := ENNReal.toReal_pos hH.ne' hfinite

/-- The interior excludes both endpoints. -/
theorem limitFinite_interior_eq {H : ℝ≥0∞} (hfinite : H ≠ ⊤) :
    interior (blowupBackwardInterval H) = Ioo (-H.toReal) 0 := by
  rw [limitFinite_domain_eq hfinite, interior_Ioc]

/-- The finite Harnack restriction has the original metric and connection. -/
def limitFiniteOpenFlow {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) :
    RicciFlow 3 L.carrier.carrier (Ioo (-H.toReal) 0) :=
  Poincare.Geometry.RicciFlow.Harnack.restrictFlow L.flow
    (by rw [limitFinite_domain_eq hfinite]; exact Ioo_subset_Ioc_self)
    ordConnected_Ioo (by
      have hT := limitFinite_horizon_pos hH hfinite
      exact ⟨-3 * H.toReal / 4, ⟨by linarith, by linarith⟩,
        -H.toReal / 4, ⟨by linarith, by linarith⟩, by linarith⟩)

/-- Literal equality of the metric representatives, including at zero. -/
theorem limitFiniteOpenFlow_metric {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) (t : ℝ) :
    (limitFiniteOpenFlow hH hfinite L).metric t = L.flow.metric t := rfl

/-- The dependent connection representatives are also unchanged. -/
theorem limitFiniteOpenFlow_connection {H : ℝ≥0∞} (hH : 0 < H) (hfinite : H ≠ ⊤)
    (L : BlowupLimitFlow.{u} (blowupBackwardInterval H)) (t : ℝ) :
    HEq ((limitFiniteOpenFlow hH hfinite L).connection t) (L.flow.connection t) := HEq.rfl

/-- Nonnegative scalar at every actual valid time, including zero. -/
theorem limitFinite_scalar_nonneg (h04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (t : ℝ) (ht : t ∈ J)
    (x : L.carrier.carrier) : 0 ≤ (L.flow.connection t).scalarCurvature x :=
  ((L.flow.connection t).curvatureOperatorBound_scalarCurvature
    (h04.tensor_calculus 3 L.carrier.carrier (L.flow.metric t) (L.flow.connection t))
    x (L.nonnegative_curvature_operator t ht x)).1

/-- Singleton compactness supplies the per-time operator ceiling. -/
theorem limitFinite_slice_operator_bound (h04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (t : ℝ) (ht : t ∈ J) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x : L.carrier.carrier,
      (L.flow.connection t).CurvatureOperatorBound K x := by
  obtain ⟨B, hB, hbound⟩ := L.curvature_locally_bounded_in_time {t}
    isCompact_singleton (singleton_subset_iff.mpr ht)
  refine ⟨3 * B, by positivity, fun x A hA => ?_⟩
  have hscalar : (L.flow.connection t).scalarCurvature x ≤ 3 * B :=
    ((L.flow.connection t).scalarCurvature_le_curvatureTensorNorm_sharp x).trans
      (mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (hbound t (mem_singleton t) x)) (by norm_num))
  have hop := ((L.flow.connection t).curvatureOperatorBound_scalarCurvature
    (h04.tensor_calculus 3 L.carrier.carrier (L.flow.metric t) (L.flow.connection t))
    x (L.nonnegative_curvature_operator t ht x)).2 A hA
  exact hop.trans (mul_le_mul_of_nonneg_right hscalar
    (Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- Both Ricci inequalities use the actual Levi-Civita connection. -/
theorem limitFinite_ricci_bounds (h04 : RicciFlowCurvatureTheory.{u})
    {J : Set ℝ} (L : BlowupLimitFlow.{u} J) (t : ℝ) (ht : t ∈ J)
    (x : L.carrier.carrier) (v : TangentSpace (𝓡 3) x) :
    0 ≤ (L.flow.connection t).ricci x v v ∧
      (L.flow.connection t).ricci x v v ≤
        (L.flow.connection t).scalarCurvature x * (L.flow.metric t).inner x v v :=
  (L.flow.connection t).ricci_bounds_of_nonnegative_curvatureOperator
    (h04.tensor_calculus 3 L.carrier.carrier (L.flow.metric t) (L.flow.connection t))
    x (L.nonnegative_curvature_operator t ht x) v

end PoincareMT.M47
