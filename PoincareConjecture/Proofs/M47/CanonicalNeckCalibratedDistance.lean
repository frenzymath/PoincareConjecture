import PoincareConjecture.Proofs.M47.CanonicalNeckCalibratedMetric
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] [MeasurableSpace M] [BorelSpace M]
  [T2Space M] [T3Space M]

private theorem static_neck_distance_coefficient {epsilon : ℝ}
    (hepsilon : 0 < epsilon) (hsmall : epsilon ≤ 1 / 200) :
    Real.sqrt (1 + epsilon) * (Real.sqrt 2 * Real.pi + epsilon⁻¹) ≤
      (21 / 20 : ℝ) * epsilon⁻¹ := by
  have hroot : Real.sqrt (1 + epsilon) ≤ 101 / 100 := by
    have hs := Real.sq_sqrt (show 0 ≤ 1 + epsilon by linarith)
    nlinarith [Real.sqrt_nonneg (1 + epsilon)]
  have htwo : Real.sqrt 2 ≤ 3 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hsphere : Real.sqrt 2 * Real.pi ≤ 6 := by
    have h := mul_le_mul htwo Real.pi_lt_four.le Real.pi_pos.le
      (by norm_num : (0 : ℝ) ≤ 3 / 2)
    norm_num at h ⊢
    exact h
  have hscaled : Real.sqrt 2 * Real.pi * epsilon ≤ 3 / 100 := by
    have h := mul_le_mul_of_nonneg_right hsphere hepsilon.le
    linarith
  have hfactor : Real.sqrt (1 + epsilon) * (Real.sqrt 2 * Real.pi * epsilon + 1) ≤
      21 / 20 := by
    have h := mul_le_mul hroot (show Real.sqrt 2 * Real.pi * epsilon + 1 ≤ 103 / 100
      by linarith) (by positivity) (by norm_num : (0 : ℝ) ≤ 101 / 100)
    nlinarith only [h]
  apply (mul_le_mul_iff_right₀ hepsilon).mp
  have hleft : epsilon * (Real.sqrt (1 + epsilon) * (Real.sqrt 2 * Real.pi + epsilon⁻¹)) =
      Real.sqrt (1 + epsilon) * (Real.sqrt 2 * Real.pi * epsilon + 1) := by
    field_simp
  have hright : epsilon * ((21 / 20 : ℝ) * epsilon⁻¹) = 21 / 20 := by field_simp
  rw [hleft, hright]
  exact hfactor

theorem neck_center_distance_calibrated {g : RiemannianMetric 3 M}
    (N : EpsilonNeck g) (hsmall : N.epsilon ≤ 1 / 200)
    {x : M} (hx : x ∈ N.carrier) :
    g.edist N.center x ≤ ENNReal.ofReal ((21 / 20 : ℝ) * N.epsilon⁻¹ * N.scale) := by
  have hscale := N.scale_pos
  have hepsilon := N.epsilon_pos
  let : Bundle.RiemannianBundle (TangentSpace (𝓡 3) : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let z := N.coordinate_inverse x
  have hz : z.2 ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    (N.coordinate_inverse_mem x hx).2
  have hzero : (0 : ℝ) ∈ Ioo (-N.epsilon⁻¹) N.epsilon⁻¹ :=
    ⟨neg_neg_of_pos (inv_pos.mpr N.epsilon_pos), inv_pos.mpr N.epsilon_pos⟩
  have hcoord : N.coordinate_map z = x := by
    have h := congrArg Subtype.val (N.coordinate_inverse_right x hx)
    rwa [N.coordinate_map_eq] at h
  have hcentral : N.coordinate_map (z.1, 0) ∈ N.central_sphere := by
    rw [N.central_sphere_eq]
    exact ⟨(z.1, 0), ⟨mem_univ _, rfl⟩, rfl⟩
  have haxial := N.edist_coordinate_map_axis_le z.1 hzero hz
  simp only [sub_zero] at haxial
  rw [Prod.eta z, hcoord] at haxial
  have haxis : N.scale * Real.sqrt (1 + N.epsilon) * |z.2| ≤
      N.scale * Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹ :=
    mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hz.1.le, hz.2.le⟩) (by positivity)
  calc
    g.edist N.center x ≤ g.edist N.center (N.coordinate_map (z.1, 0)) +
        g.edist (N.coordinate_map (z.1, 0)) x := Manifold.riemannianEDist_triangle
    _ ≤ ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * Real.sqrt 2 * Real.pi) +
        ENNReal.ofReal (N.scale * Real.sqrt (1 + N.epsilon) * N.epsilon⁻¹) :=
      add_le_add (N.edist_central_sphere_le N.center_on_central_sphere hcentral)
        (haxial.trans (ENNReal.ofReal_le_ofReal haxis))
    _ = ENNReal.ofReal
        ((Real.sqrt (1 + N.epsilon) * (Real.sqrt 2 * Real.pi + N.epsilon⁻¹)) * N.scale) := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (static_neck_distance_coefficient N.epsilon_pos hsmall) N.scale_pos.le)

theorem ordinary_closed_neck_center_distance_calibrated {J : Set ℝ}
    (G : RicciFlow 3 M J) (T : ℝ)
    (N : EpsilonNeck (G.metric T)) (hsmall : N.epsilon ≤ 1 / 200)
    (hcarrier : N.carrier = univ)
    (hclock : ∀ s ∈ Icc (-1 : ℝ) 0, T + s / (N.scale⁻¹ ^ 2) ∈ J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => (N.scale⁻¹ ^ 2) * roundCylinderPullback
        (G.metric (T + s / (N.scale⁻¹ ^ 2))) N.coordinate_map z v w))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : M) :
    (G.metric (T + s / (N.scale⁻¹ ^ 2))).edist N.center x ≤
      ENNReal.ofReal ((5 / 2 : ℝ) * N.epsilon⁻¹ * N.scale) := by
  have hbound (y : M) (v : TangentSpace (𝓡 3) y) :
      (G.metric (T + s / (N.scale⁻¹ ^ 2))).inner (id y)
        (mfderiv (𝓡 3) (𝓡 3) id y v) (mfderiv (𝓡 3) (𝓡 3) id y v) ≤
          (23 / 10 : ℝ) ^ 2 * (G.metric T).inner y v v := by
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
    exact ordinary_closed_neck_metric_le_calibrated G T N hsmall hclock hfamily s hs y
      (hcarrier.symm ▸ mem_univ y) v
  have hd := (G.metric T).edist_le_mul_of_inner_mfderiv_le
    (G.metric (T + s / (N.scale⁻¹ ^ 2))) contMDiff_id
    (by norm_num : (0 : ℝ) < 23 / 10) hbound N.center x
  have hdiam := neck_center_distance_calibrated N hsmall (hcarrier.symm ▸ mem_univ x)
  calc
    _ ≤ ENNReal.ofReal (23 / 10 : ℝ) * (G.metric T).edist N.center x := hd
    _ ≤ ENNReal.ofReal (23 / 10 : ℝ) *
        ENNReal.ofReal ((21 / 20 : ℝ) * N.epsilon⁻¹ * N.scale) :=
      mul_le_mul_right hdiam _
    _ = ENNReal.ofReal ((483 / 200 : ℝ) * N.epsilon⁻¹ * N.scale) := by
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by norm_num)
        (inv_pos.mpr N.epsilon_pos).le) N.scale_pos.le)

theorem strongNeck_closed_center_distance_calibrated (P : M47Predecessors.{u})
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
    (F.metric (T + s / 1)).edist (E.forward s hs N.neck.center) (E.forward s hs x.val) ≤
      ENNReal.ofReal ((5 / 2 : ℝ) * epsilon⁻¹ * N.neck.scale) := by
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
  obtain ⟨N0, hepsilon, hscale, _hconnection, hcenter0, hcarrier, hcoordinate⟩ :=
    exists_full_open_source_neck N.neck U hU (G.metric T) (G.connection T) hterminal
  have htimes : ∀ v ∈ Ioc (-1 : ℝ) 0, v / Q ∈ Icc (-Q⁻¹) 0 := by
    intro v hv
    have hp := strongNeckPhysicalClock_parameter N hv
    exact ⟨hp.1.le, hp.2⟩
  have hfamily := strongNeck_original_ordinary_family N U hU E G
    (fun v hv y w w' => (hread v hv y).1 w w') htimes hagree
    N0 hepsilon hscale hcoordinate
  have hclock (v : ℝ) (hv : v ∈ Icc (-1 : ℝ) 0) :
      T + v / (N0.scale⁻¹ ^ 2) ∈ Icc (T + -Q⁻¹) (T + 0) := by
    rw [hscale]
    have hlo := div_le_div_of_nonneg_right hv.1 hQ.le
    have hhi : v / Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hv.2 hQ.le
    simp only [neg_div, one_div] at hlo
    constructor <;> linarith only [hlo, hhi]
  have hparam : Q * s ∈ Icc (-1 : ℝ) 0 := by
    have hlo := mul_le_mul_of_nonneg_left hs.1 hQ.le
    have hcancel : Q * (-Q⁻¹) = -1 := by field_simp
    rw [hcancel] at hlo
    exact ⟨hlo, mul_nonpos_of_nonneg_of_nonpos hQ.le hs.2⟩
  have hclock' : T + Q * s / (N0.scale⁻¹ ^ 2) = T + s / 1 := by
    rw [hscale, mul_div_cancel_left₀ _ hQ.ne', div_one]
  have hNsmall : N0.epsilon ≤ 1 / 200 := by
    rw [hepsilon, N.epsilon_eq]
    exact hsmall
  have hd := ordinary_closed_neck_center_distance_calibrated G T N0 hNsmall hcarrier
    hclock hfamily (Q * s) hparam x
  rw [hclock', hepsilon, N.epsilon_eq, hscale] at hd
  have hforward : ContMDiff (𝓡 3) (𝓡 3) ∞
      (fun y : U => E.forward s hs y.val) := by
    intro y
    exact ((E.forward_smooth s hs y.val y.property).contMDiffAt
      (U.isOpen.mem_nhds y.property)).comp y (contMDiff_subtype_val y)
  have hpull := (G.metric (T + s / 1)).edist_le_mul_of_inner_mfderiv_le
    (F.metric (T + s / 1)) (hforward.of_le (by simp)) (by norm_num : (0 : ℝ) < 1)
    (fun y v => by simpa only [one_pow, one_mul] using ((hread s hs y).1 v v).le)
    N0.center x
  simp only [ENNReal.ofReal_one, one_mul] at hpull
  rw [hcenter0] at hpull
  exact hpull.trans hd

end PoincareConjecture.Proofs.M47
