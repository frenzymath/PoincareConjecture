import PoincareConjecture.Proofs.M47.CanonicalNeckClosedScalarComparison









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47



theorem strongNeck_closed_scalar_difference_le (P : M47Predecessors.{u})
    {F : SurgeryFlowData.{u}} {T epsilon : ℝ}
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
    (s : ℝ) (hs : s ∈ Icc (-(N.neck.scale⁻¹ ^ 2)⁻¹) 0) (x : U) :
    |(F.connection (T + s / 1)).scalarCurvature (E.forward s hs x.val) /
        (N.neck.scale⁻¹ ^ 2) - 1 / (1 - (N.neck.scale⁻¹ ^ 2) * s)| ≤
      (16 / 5 : ℝ) * epsilon := by
  let Q := N.neck.scale⁻¹ ^ 2
  have hQ : 0 < Q := N.cylinder.scale_pos
  have hbottom : -Q⁻¹ < (0 : ℝ) := neg_neg_of_pos (inv_pos.mpr hQ)
  have hzero : (0 : ℝ) ∈ Icc (-Q⁻¹) 0 := ⟨hbottom.le, le_rfl⟩
  have hcenter : N.neck.center ∈ (U : Set (F.slice T).carrier) := by
    rw [hU]
    exact N.neck.central_sphere_subset N.neck.center_on_central_sphere
  obtain ⟨G, hread⟩ := exists_buffered_cylinder_ordinary P hbottom U
    ⟨N.neck.center, hcenter⟩ E
  have hterminal := neck_ordinary_terminal_metric U E hzero hbased G
    (fun y v w => (hread 0 hzero y).1 v w)
  obtain ⟨N0, hepsilon, hscale, _hconnection, _hcenter0, hcarrier, hcoordinate⟩ :=
    exists_full_open_source_neck N.neck U hU (G.metric T) (G.connection T) hterminal
  have htimes : ∀ v ∈ Ioc (-1 : ℝ) 0, v / Q ∈ Icc (-Q⁻¹) 0 := by
    intro v hv
    have hp := strongNeckPhysicalClock_parameter N hv
    exact ⟨hp.1.le, hp.2⟩
  have hfamily := strongNeck_original_ordinary_family N U hU E G
    (fun v hv y w w' => (hread v hv y).1 w w') htimes hagree
    N0 hepsilon hscale hcoordinate
  have hfamily' : RoundCylinderFamilyClose N0.epsilon (Ioc (-1 : ℝ) 0)
      (fun v z w w' => Q * roundCylinderPullback
        (G.metric (T + v / Q)) N0.coordinate_map z w w') := by
    simpa only [hscale] using hfamily
  have hclock (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0) :
      T + v / Q ∈ Icc (T + -Q⁻¹) (T + 0) := by
    have hlo := div_le_div_of_nonneg_right hv.1 hQ.le
    have hhi : v / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.2 hQ.le
    simp only [neg_div, one_div] at hlo
    constructor <;> linarith only [hlo, hhi]
  have hparam : Q * s ∈ Icc (-1 : ℝ) 0 := by
    have hlo := mul_le_mul_of_nonneg_left hs.1 hQ.le
    have hcancel : Q * (-Q⁻¹) = -1 := by field_simp
    rw [hcancel] at hlo
    exact ⟨hlo, mul_nonpos_of_nonneg_of_nonpos hQ.le hs.2⟩
  have hclock' : T + Q * s / Q = T + s / 1 := by
    rw [mul_div_cancel_left₀ _ hQ.ne', div_one]
  have hNsmall : N0.epsilon ≤ 1 / 200 := by
    rw [hepsilon, N.epsilon_eq]
    exact hsmall
  have hx : x ∈ N0.carrier := hcarrier.symm ▸ mem_univ x
  have h := ordinary_closed_neck_scalar_difference_le P.m04 G T N0 hNsmall hQ
    hclock hfamily' (Q * s) hparam x hx
  rw [hclock', (hread s hs x).2.1, hepsilon, N.epsilon_eq] at h
  exact h

end PoincareConjecture.Proofs.M47
