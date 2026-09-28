import PoincareConjecture.Proofs.Ch01.CurvatureConnection
import PoincareConjecture.Proofs.Horizon.Topology.Manifold.NeckCap.Cap.Boundary
import PoincareConjecture.Proofs.Horizon.Geometry.Riemannian.Connection.Uniqueness
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Geodesic.Calibration











set_option autoImplicit false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.CapCertificate

variable {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T3Space M] {g : RiemannianMetric 3 M}
  (C : CapCertificate g)

theorem scalar_lt_constant_mul {x y : M} (hx : x ∈ C.carrier)
    (hy : y ∈ C.carrier) :
    C.connection.scalarCurvature y < C.cap_constant * C.connection.scalarCurvature x := by
  obtain ⟨b, hb, hratio⟩ := C.scalar_ratio
  exact (hratio x hx y hy).trans_lt
    (mul_lt_mul_of_pos_right hb (C.scalar_pos x hx))

theorem scalar_range_bddAbove :
    BddAbove (range (fun y : C.carrier => C.connection.scalarCurvature y.val)) := by
  obtain ⟨x, hx⟩ := C.core_nonempty
  refine ⟨C.cap_constant * C.connection.scalarCurvature x, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact (C.scalar_lt_constant_mul (C.core_subset_carrier hx) y.property).le

theorem scalar_le_sup {x : M} (hx : x ∈ C.carrier) :
    C.connection.scalarCurvature x ≤ scalarCurvatureSupOn g C.connection C.carrier := by
  exact le_csSup C.scalar_range_bddAbove ⟨⟨x, hx⟩, rfl⟩

theorem scalar_sup_pos : 0 < scalarCurvatureSupOn g C.connection C.carrier := by
  obtain ⟨x, hx⟩ := C.core_nonempty
  exact (C.scalar_pos x (C.core_subset_carrier hx)).trans_le
    (C.scalar_le_sup (C.core_subset_carrier hx))

theorem scalar_sup_le_constant_mul {x : M} (hx : x ∈ C.carrier) :
    scalarCurvatureSupOn g C.connection C.carrier ≤
      C.cap_constant * C.connection.scalarCurvature x := by
  unfold scalarCurvatureSupOn
  refine csSup_le ?_ ?_
  · exact ⟨C.connection.scalarCurvature x, ⟨⟨x, hx⟩, rfl⟩⟩
  · rintro _ ⟨y, rfl⟩
    exact (C.scalar_lt_constant_mul hx y.property).le

theorem intrinsic_diameter_lt_at_point {x : M} (hx : x ∈ C.carrier) :
    intrinsicDiameter g C.carrier <
      ENNReal.ofReal (C.cap_constant * C.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  apply C.intrinsic_diameter_bound.trans_le
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_nonpos (C.scalar_pos x hx) (C.scalar_le_sup hx) (by norm_num))
    C.cap_constant_pos.le

theorem intrinsic_diameter_lt_of_constant_le {B : ℝ} (hB : C.cap_constant ≤ B)
    {x : M} (hx : x ∈ C.carrier) :
    intrinsicDiameter g C.carrier <
      ENNReal.ofReal (B * C.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  apply (C.intrinsic_diameter_lt_at_point hx).trans_le
  exact ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right hB (Real.rpow_nonneg (C.scalar_pos x hx).le _))

theorem edist_lt_at_point {B : ℝ} (hB : C.cap_constant ≤ B)
    {x y : M} (hx : x ∈ C.carrier) (hy : y ∈ C.carrier) :
    g.edist x y <
      ENNReal.ofReal (B * C.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  have hdiam : intrinsicEDist g C.carrier x y ≤ intrinsicDiameter g C.carrier :=
    le_sSup ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩
  exact ((g.edist_le_intrinsicEDist C.carrier x y).trans hdiam).trans_lt
    (C.intrinsic_diameter_lt_of_constant_le hB hx)



theorem edist_le_of_mem_closure [T2Space M] {B : ℝ} (hB : C.cap_constant ≤ B)
    {x y : M} (hx : x ∈ C.carrier) (hy : y ∈ closure C.carrier) :
    g.edist x y ≤
      ENNReal.ofReal (B * C.connection.scalarCurvature x ^ (-1 / 2 : ℝ)) := by
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 3))
      (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨⟨g.inner, g.toContinuousRiemannianMetric.continuous, fun _ _ _ => rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric (𝓡 3) M
  exact closure_minimal (fun z hz => (C.edist_lt_at_point hB hx hz).le)
    (isClosed_le (continuous_const.edist continuous_id) continuous_const) hy

theorem end_scale_lower_at_point {x : M} (hx : x ∈ C.carrier) :
    (C.cap_constant * C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ) <
      C.end_neck.scale := by
  rw [C.end_neck.scale_eq_scalar, C.end_neck_connection]
  have hc := C.end_neck_subset
    (C.end_neck.central_sphere_subset C.end_neck.center_on_central_sphere)
  apply Real.rpow_lt_rpow_of_neg
    (C.scalar_pos _ hc) (C.scalar_lt_constant_mul hx hc)
  norm_num

theorem boundary_scale_lower_at_point {x : M} (hx : x ∈ C.carrier) :
    (C.cap_constant * C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ) <
      C.boundary_neck.scale := by
  rw [C.boundary_neck.scale_eq_scalar, C.boundary_neck_connection]
  have hc := C.boundary_neck_subset
    (C.boundary_neck.central_sphere_subset C.boundary_neck.center_on_central_sphere)
  apply Real.rpow_lt_rpow_of_neg
    (C.scalar_pos _ hc) (C.scalar_lt_constant_mul hx hc)
  norm_num



theorem neck_scales_lower_of_constant_le {B : ℝ} (hB : C.cap_constant ≤ B)
    {x : M} (hx : x ∈ C.carrier) :
    (B * C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ) < C.end_neck.scale ∧
      (B * C.connection.scalarCurvature x) ^ (-1 / 2 : ℝ) < C.boundary_neck.scale := by
  have hpow := Real.rpow_le_rpow_of_nonpos
    (mul_pos C.cap_constant_pos (C.scalar_pos x hx))
    (mul_le_mul_of_nonneg_right hB (C.scalar_pos x hx).le)
    (by norm_num : (-1 / 2 : ℝ) ≤ 0)
  exact ⟨hpow.trans_lt (C.end_scale_lower_at_point hx),
    hpow.trans_lt (C.boundary_scale_lower_at_point hx)⟩



theorem uniform_bounds_at_point (D : LeviCivitaData g) {B : ℝ}
    (hB : C.cap_constant ≤ B) {x : M} (hx : x ∈ C.carrier) :
    intrinsicDiameter g C.carrier <
        ENNReal.ofReal (B * D.scalarCurvature x ^ (-1 / 2 : ℝ)) ∧
      (B * D.scalarCurvature x) ^ (-1 / 2 : ℝ) < C.end_neck.scale ∧
      (B * D.scalarCurvature x) ^ (-1 / 2 : ℝ) < C.boundary_neck.scale := by
  rw [← C.connection.scalarCurvature_eq D x]
  exact ⟨C.intrinsic_diameter_lt_of_constant_le hB hx,
    C.neck_scales_lower_of_constant_le hB hx⟩

end PoincareConjecture.CapCertificate
