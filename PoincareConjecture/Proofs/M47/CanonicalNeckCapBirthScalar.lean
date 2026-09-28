import PoincareConjecture.Proofs.M47.CanonicalNeckCapScalarRatio
import PoincareConjecture.Proofs.M47.CanonicalNeckPhysicalScalarComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

theorem cap_birth_scalar_le_initial
    {F : SurgeryFlowData.{u}}
    (standard : RepairedStandardCapExistenceData F.standard_initial)
    {t : ℝ} {hT : t ∈ F.surgery_times} [Nonempty (F.slice t).carrier]
    {i : Fin (F.event t hT).cap_count} {A eta : ℝ} {J : Set ℝ}
    {U : Set (F.slice t).carrier}
    (e : SurgeryFlowCylinder F (F.slice t) t ((F.parameters.h t)⁻¹ ^ 2) J U)
    (initial : SurgeryCapInitialComparison F t hT i A)
    (comparison : SurgeryCapFamilyComparison F standard.flow A eta e initial.chart)
    (hzero : (0 : ℝ) ∈ J)
    (hbase : ∀ y ∈ U, HEq (e.forward 0 hzero y) y)
    (hratio : ∀ z ∈ F.standard_initial.metric.ball 0 A,
      (F.parameters.h t) ^ 2 *
        (F.connection (t + 0 / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
          (e.forward 0 hzero (initial.chart z)) ≤
        (101 / 100 : ℝ) * (standard.flow.connection 0).scalarCurvature z)
    {y : (F.slice t).carrier} (hy : y ∈ U) :
    (F.parameters.h t) ^ 2 * (F.connection t).scalarCurvature y ≤
      (101 / 100 : ℝ) * standard.initial_estimate.scalar_constant := by
  have himage : initial.chart '' F.standard_initial.metric.ball 0 A = U :=
    comparison.choose_spec.2.2.2.1
  obtain ⟨z, hz, rfl⟩ := himage.symm ▸ hy
  have hpoint : (⟨t + 0 / ((F.parameters.h t)⁻¹ ^ 2),
      e.forward 0 hzero (initial.chart z)⟩ : Σ s, (F.slice s).carrier) =
      ⟨t, initial.chart z⟩ := Sigma.ext (by simp) (hbase _ hy)
  have hscalar := congrArg
    (fun p : Σ s, (F.slice s).carrier => (F.connection p.1).scalarCurvature p.2) hpoint
  have h := hratio z hz
  change (F.connection (t + 0 / ((F.parameters.h t)⁻¹ ^ 2))).scalarCurvature
      (e.forward 0 hzero (initial.chart z)) =
        (F.connection t).scalarCurvature (initial.chart z) at hscalar
  rw [hscalar] at h
  have hinitial : (⟨standard.flow.metric 0, standard.flow.connection 0⟩ :
      Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g) =
      ⟨F.standard_initial.metric, F.standard_initial.connection⟩ :=
    Sigma.ext standard.flow.base.initial_metric standard.flow.base.initial_connection
  have hstandardScalar := congrArg
    (fun p : Σ g : RiemannianMetric 3 StandardCapSpace, LeviCivitaData g =>
      p.2.scalarCurvature z) hinitial
  change (standard.flow.connection 0).scalarCurvature z =
    F.standard_initial.connection.scalarCurvature z at hstandardScalar
  rw [hstandardScalar] at h
  exact h.trans (mul_le_mul_of_nonneg_left
    (standard.initial_estimate.scalar_bounds z).2 (by norm_num))

theorem strongNeck_scale_mul_height_sq_le
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}} {T epsilon : ℝ}
    (N : SurgeryStrongNeck F T epsilon) (hsmall : epsilon ≤ 1 / 200)
    (U : TopologicalSpace.Opens (F.slice T).carrier)
    (hU : (U : Set (F.slice T).carrier) = N.neck.carrier)
    (E : SurgeryFlowCylinder F (F.slice T) T 1
      (Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) U)
    (hbased : ∀ hs x, x ∈ U → HEq (E.forward 0 hs x) x)
    (hagree : ∀ s (hs : s ∈ Ioc (-1 : ℝ) 0)
      (hs' : s / (N.neck.scale⁻¹ ^ 2) ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0),
      ∀ x ∈ U,
        HEq (E.forward (s / (N.neck.scale⁻¹ ^ 2)) hs' x) (N.cylinder.forward s hs x))
    {D h : ℝ} (hD : 0 < D)
    (hupper :
      let a := -(N.neck.scale⁻¹ ^ 2)⁻¹
      let ha : a ∈ Icc a 0 :=
        ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr N.cylinder.scale_pos).le⟩
      h ^ 2 * (F.connection (T + a / 1)).scalarCurvature
        (E.forward a ha N.neck.center) ≤ (101 / 100 : ℝ) * D) :
    (N.neck.scale⁻¹ ^ 2) * h ^ 2 ≤ 8 * D := by
  let Q := N.neck.scale⁻¹ ^ 2
  have hQ : 0 < Q := N.cylinder.scale_pos
  have ha : -Q⁻¹ ∈ Icc (-Q⁻¹) 0 :=
    ⟨le_rfl, neg_nonpos.mpr (inv_pos.mpr hQ).le⟩
  have hcenter : N.neck.center ∈ (U : Set (F.slice T).carrier) := by
    rw [hU]
    exact N.neck.central_sphere_subset N.neck.center_on_central_sphere
  have herror := strongNeck_closed_scalar_difference_le P N hsmall U hU E hbased hagree
    (-Q⁻¹) ha ⟨N.neck.center, hcenter⟩
  have hcancel : Q * (-Q⁻¹) = -1 := by field_simp
  change |(F.connection (T + -Q⁻¹ / 1)).scalarCurvature
    (E.forward (-Q⁻¹) ha N.neck.center) / Q - 1 / (1 - Q * (-Q⁻¹))| ≤
      (16 / 5 : ℝ) * epsilon at herror
  rw [hcancel] at herror
  norm_num only [sub_neg_eq_add, one_add_one_eq_two] at herror
  have hlower := (scalar_bottom_bounds_of_cylinder_error hQ hsmall herror).1
  have hscaled := mul_le_mul_of_nonneg_left hlower (sq_nonneg h)
  dsimp only at hupper
  change Q * h ^ 2 ≤ 8 * D
  nlinarith only [hscaled, hupper, hD]

end PoincareConjecture.Proofs.M47
