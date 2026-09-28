import PoincareConjecture.Proofs.M47.CanonicalNeckCoarseMetric
import PoincareConjecture.Proofs.M47.CanonicalNeckClosedScalar
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.CanonicalNeighborhood.Neck.Separation.Diameter










set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter
open scoped Manifold ContDiff Topology Bundle ENNReal

universe u

namespace PoincareConjecture.Proofs.M47

local notation "E₃" => EuclideanSpace ℝ (Fin 3)

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E₃ M]
  [IsManifold (𝓡 3) ∞ M] {J : Set ℝ}


theorem ordinary_closed_neck_metric_le (G : RicciFlow 3 M J) (T : ℝ)
    (N : EpsilonNeck (G.metric T)) (hsmall : N.epsilon ≤ 1 / 200)
    (hclock : ∀ s ∈ Icc (-1 : ℝ) 0, T + s / (N.scale⁻¹ ^ 2) ∈ J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => (N.scale⁻¹ ^ 2) * roundCylinderPullback
        (G.metric (T + s / (N.scale⁻¹ ^ 2))) N.coordinate_map z v w))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : M) (hx : x ∈ N.carrier)
    (v : TangentSpace (𝓡 3) x) :
    (G.metric (T + s / (N.scale⁻¹ ^ 2))).inner x v v ≤
      10 * (G.metric T).inner x v v := by
  have hstrict (a : ℝ) (ha : a ∈ Ioc (-1 : ℝ) 0) :
      (G.metric (T + a / (N.scale⁻¹ ^ 2))).inner x v v ≤
        10 * (G.metric T).inner x v v :=
    neck_metric_le_ten N hsmall _ ⟨ha.1.le, ha.2⟩ (hfamily.at_time ha) x hx v
  have hmetric : ContinuousOn (fun t : ℝ => (G.metric t).inner x v v) J :=
    fun t ht => (G.equation t ht x v v).continuousWithinAt
  have hcont : ContinuousOn
      (fun a : ℝ => (G.metric (T + a / (N.scale⁻¹ ^ 2))).inner x v v)
      (Icc (-1 : ℝ) 0) :=
    hmetric.comp (by fun_prop) hclock
  have hclosure : closure (Ioc (-1 : ℝ) 0) = Icc (-1 : ℝ) 0 :=
    closure_Ioc (by norm_num)
  exact le_on_closure hstrict (hclosure.symm ▸ hcont) continuousOn_const
    (hclosure.symm ▸ hs)

variable [MeasurableSpace M] [BorelSpace M] [T2Space M] [T3Space M]


theorem ordinary_closed_neck_center_distance (G : RicciFlow 3 M J) (T : ℝ)
    (N : EpsilonNeck (G.metric T)) (hsmall : N.epsilon ≤ 1 / 200)
    (hcarrier : N.carrier = univ)
    (hclock : ∀ s ∈ Icc (-1 : ℝ) 0, T + s / (N.scale⁻¹ ^ 2) ∈ J)
    (hfamily : RoundCylinderFamilyClose N.epsilon (Ioc (-1 : ℝ) 0)
      (fun s z v w => (N.scale⁻¹ ^ 2) * roundCylinderPullback
        (G.metric (T + s / (N.scale⁻¹ ^ 2))) N.coordinate_map z v w))
    (s : ℝ) (hs : s ∈ Icc (-1 : ℝ) 0) (x : M) :
    (G.metric (T + s / (N.scale⁻¹ ^ 2))).edist N.center x ≤
      ENNReal.ofReal (4 * (2 * Real.pi + 2 * N.epsilon⁻¹) * N.scale) := by
  have hbound (y : M) (v : TangentSpace (𝓡 3) y) :
      (G.metric (T + s / (N.scale⁻¹ ^ 2))).inner (id y)
        (mfderiv (𝓡 3) (𝓡 3) id y v) (mfderiv (𝓡 3) (𝓡 3) id y v) ≤
          (4 : ℝ) ^ 2 * (G.metric T).inner y v v := by
    simp only [id_eq, mfderiv_id, ContinuousLinearMap.id_apply]
    have h := ordinary_closed_neck_metric_le G T N hsmall hclock hfamily s hs y
      (hcarrier.symm ▸ mem_univ y) v
    have hnonneg : 0 ≤ (G.metric T).inner y v v := by
      by_cases hv : v = 0
      · simp [hv]
      · exact ((G.metric T).pos y v hv).le
    nlinarith only [h, hnonneg]
  have hd := (G.metric T).edist_le_mul_of_inner_mfderiv_le
    (G.metric (T + s / (N.scale⁻¹ ^ 2))) contMDiff_id (by norm_num : (0 : ℝ) < 4)
    hbound N.center x
  have hdiam := N.edist_center_le_of_mem_carrier (hcarrier.symm ▸ mem_univ x)
  calc
    _ ≤ ENNReal.ofReal 4 * (G.metric T).edist N.center x := hd
    _ ≤ ENNReal.ofReal 4 *
        ENNReal.ofReal ((2 * Real.pi + 2 * N.epsilon⁻¹) * N.scale) :=
      mul_le_mul_right hdiam _
    _ = _ := by rw [← ENNReal.ofReal_mul (by norm_num)]; congr 1; ring


theorem strongNeck_closed_center_distance (P : M47Predecessors.{u})
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
      ENNReal.ofReal (4 * (2 * Real.pi + 2 * epsilon⁻¹) * N.neck.scale) := by
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
  have hd := ordinary_closed_neck_center_distance G T N0 hNsmall hcarrier
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
