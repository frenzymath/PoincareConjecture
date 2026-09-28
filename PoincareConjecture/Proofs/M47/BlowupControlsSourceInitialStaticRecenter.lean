import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOwnScalar
import PoincareConjecture.Proofs.M47.BlowupControlsSourceInitialOlderCarrier
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineComparison
import PoincareConjecture.Proofs.M47.BlowupControlsCapAffineFields











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M47




theorem exists_source_initial_static_recentered_neck
    {F : SurgeryFlowData.{u}} {t : ℝ} (hT : t ∈ F.surgery_times)
    [Nonempty (F.slice t).carrier] (i : Fin (F.event t hT).cap_count)
    {A : ℝ} (initial : SurgeryCapInitialComparison F t hT i A)
    {U : Set StandardCapSpace}
    (hsource : U ⊆ F.standard_initial.metric.ball 0 A)
    (havoid : ∀ x ∈ U, initial.chart x ∉ ((F.event t hT).caps i).carrier)
    {x : StandardCapSpace} (hx : x ∈ U)
    {r W epsilon : ℝ} (hxR : x ∈ F.standard_initial.metric.ball 0 r)
    (hr : 0 < r) (hW : 0 < W) (hA : r + 2 < A)
    (hmargin : (((F.event t hT).necks i).neck.coordinate_inverse
      (sourceInitialOldMap initial x)).2 + W < 0)
    (hdelta : 4 * r + W + 4 < ((F.event t hT).necks i).neck.epsilon⁻¹)
    (hwidth : epsilon⁻¹ ≤ W) (hepsilon : 0 < epsilon)
    (hepsilon_lt : epsilon < 1 / 2)
    (hdomain : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      s + (((F.event t hT).necks i).neck.coordinate_inverse
        (sourceInitialOldMap initial x)).2 ∈
        Ioo (-((F.event t hT).necks i).neck.epsilon⁻¹)
          (((F.event t hT).necks i).neck.epsilon⁻¹))
    {q k R_join : ℝ} (hq : 0 < q)
    (hqscale : q = ((F.event t hT).necks i).neck.scale⁻¹ ^ 2)
    (hown : k ∈ Icc (3 / 4 : ℝ) (5 / 4) ∧
      MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0)
        (Icc (-1 - W) 0))
    (hjoin : q * k = R_join)
    (hR : R_join = ((F.event t hT).necks i).neck.connection.scalarCurvature
      (sourceInitialOldMap initial x))
    (hscalar : 0 < ((F.event t hT).necks i).neck.connection.scalarCurvature
      (sourceInitialOldMap initial x))
    {B : ℝ → RoundCylinderTwoTensor}
    (hBzero : B 0 = fun z v w => q * roundCylinderPullback
      (F.event t hT).limit_metric
      ((F.event t hT).necks i).neck.coordinate_map z v w)
    (hfamily : RoundCylinderFamilyClose epsilon (Icc (-1 : ℝ) 0)
      (fun u z v w => k * neckAxialTensorPullback 1
        (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial x)).2
        (B (u / k)) z v w)) :
    ∃ E : EpsilonNeck (F.event t hT).limit_metric,
      ∃ V : Set ((F.event t hT).terminal.carrier),
      E.epsilon = epsilon ∧
      E.connection = ((F.event t hT).necks i).neck.connection ∧
      E.center = sourceInitialOldMap initial x ∧
      E.carrier = ((F.event t hT).necks i).neck.region
        ((((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial x)).2 - epsilon⁻¹)
        ((((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial x)).2 + epsilon⁻¹) ∧
      E.coordinate_map = ((F.event t hT).necks i).neck.coordinate_map ∘
        neckAxialSpaceMap 1 (((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial x)).2 ∧
      E.coordinate_inverse = neckAxialInverse 1
          (((F.event t hT).necks i).neck.coordinate_inverse
            (sourceInitialOldMap initial x)).2 ∘
        ((F.event t hT).necks i).neck.coordinate_inverse ∧
      E.central_sphere = ((F.event t hT).necks i).neck.coordinate_map ''
        (univ ×ˢ ({(((F.event t hT).necks i).neck.coordinate_inverse
          (sourceInitialOldMap initial x)).2} : Set ℝ)) ∧
      E.carrier ⊆ V ∧
      V ⊆ ((F.event t hT).necks i).neck.region
        (-((F.event t hT).necks i).neck.epsilon⁻¹) 0 ∧
      q = ((F.event t hT).necks i).neck.scale⁻¹ ^ 2 ∧
      0 < q * k ∧
      MapsTo (fun u : ℝ => u / k) (Icc (-1 : ℝ) 0)
        (Icc (-1 - W) 0) := by
  let N := ((F.event t hT).necks i).neck
  let y := sourceInitialOldMap initial x
  let c := (N.coordinate_inverse y).2
  let V := N.region (c - W) (c + W)
  have hdomain' : ∀ s ∈ Ioo (-epsilon⁻¹) epsilon⁻¹,
      1 * s + c ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ := by
    intro s hs
    simpa only [N, y, c, one_mul] using hdomain s hs
  have hgeom : IsOpen V ∧ y ∈ V ∧ V.Nonempty ∧
      V ⊆ N.region (-N.epsilon⁻¹) 0 ∧
      V ⊆ N.region (-(4 * r + W + 3)) (4 * r + W + 3) := by
    simpa only [N, y, c, V] using
      (source_initial_older_carrier_geometry hT i initial hr hW hA hxR
        (havoid x hx)
        hmargin hdelta)
  have hprops := source_initial_old_map_properties initial hsource havoid
  have hy : y ∈ N.carrier := (hprops.2.2 hx).1
  let qSphere : UnitTwoSphere := (N.coordinate_inverse y).1
  have hcenter : N.coordinate_map (qSphere, c) = y := by
    simpa only [qSphere, c] using M36.neck_coordinate_inverse N hy
  have hscalarCenter : 0 < N.connection.scalarCurvature
      (N.coordinate_map (qSphere, c)) := by
    simpa only [hcenter] using hscalar
  have hkpos : 0 < k := by linarith only [hown.1.1]
  have hqkpos : 0 < q * k := mul_pos hq hkpos
  have hqkScalar : q * k = N.connection.scalarCurvature y := by
    rw [hjoin, hR]
  have hzero : (0 : ℝ) ∈ Icc (-1 : ℝ) 0 := by constructor <;> norm_num
  have hclose0 : RoundCylinderClose epsilon 0
      (fun z v w => k * neckAxialTensorPullback 1 c
        (B (0 / k)) z v w) := by
    refine ⟨hfamily.1 0 hzero, ?_⟩
    rcases hfamily.2 with ⟨bound, hbound, hjet⟩
    refine ⟨bound, hbound, ?_⟩
    intro z hz
    simpa only [zero_div] using hjet 0 hzero z hz
  have hclose : RoundCylinderClose epsilon 0
      (fun z v w => N.connection.scalarCurvature (N.coordinate_map (qSphere, c)) *
        roundCylinderPullback (F.event t hT).limit_metric
          (N.coordinate_map ∘ neckAxialSpaceMap 1 c) z v w) := by
    apply hclose0.congr_cylinder
    intro z hz v w
    rw [zero_div, hBzero]
    have ha := cap_neck_affine_pullback N 1 c
      (hdomain' z.2 hz) v w
    calc
      _ = (q * k) * neckAxialTensorPullback 1 c
          (roundCylinderPullback (F.event t hT).limit_metric N.coordinate_map)
          z v w := by
        simp only [neckAxialTensorPullback]
        ring
      _ = N.connection.scalarCurvature (N.coordinate_map (qSphere, c)) *
          neckAxialTensorPullback 1 c
            (roundCylinderPullback (F.event t hT).limit_metric N.coordinate_map)
            z v w := by rw [hqkScalar, hcenter]
      _ = _ := by rw [ha]
  let E := capAffineNeck N hepsilon hepsilon_lt zero_lt_one hdomain' qSphere
    hscalarCenter hclose
  have hfields := capAffineNeck_full_fields N hepsilon hepsilon_lt zero_lt_one
    hdomain' qSphere hscalarCenter hclose
  have hcenterE := capAffineNeck_fields N hepsilon hepsilon_lt zero_lt_one
    hdomain' qSphere hscalarCenter hclose
  have hcarrier : E.carrier = N.region (c - epsilon⁻¹) (c + epsilon⁻¹) := by
    simpa only [E, one_mul] using hfields.2.2.1
  have hmap : E.coordinate_map = N.coordinate_map ∘ neckAxialSpaceMap 1 c := by
    simpa only [E] using hfields.2.2.2.1
  have hinverse : E.coordinate_inverse =
      neckAxialInverse 1 c ∘ N.coordinate_inverse := by
    simpa only [E] using hfields.2.2.2.2.1
  have hsphere : E.central_sphere = N.coordinate_map ''
      (univ ×ˢ ({c} : Set ℝ)) := by
    simpa only [E, one_mul] using hfields.2.2.2.2.2
  have hcenterY : E.center = y := by
    exact hcenterE.trans hcenter
  have hEsubV : E.carrier ⊆ V := by
    rw [hcarrier]
    intro p hp
    refine ⟨hp.1, ?_, ?_⟩
    · have hlo : c - W ≤ c - epsilon⁻¹ := by linarith only [hwidth]
      exact hlo.trans_lt hp.2.1
    · have hhi : c + epsilon⁻¹ ≤ c + W := by linarith only [hwidth]
      exact hp.2.2.trans_le hhi
  refine ⟨E, V, ?_⟩
  refine ⟨rfl, rfl, hcenterY, hcarrier, hmap, hinverse, hsphere,
    hEsubV, hgeom.2.2.2.1, hqscale, hqkpos, hown.2⟩

end PoincareConjecture.M47
