import PoincareConjecture.Proofs.M47.ComponentEstimateTip
import PoincareConjecture.Proofs.M47.ComponentEstimateCap
import PoincareConjecture.Proofs.M12.Geometry.Riemannian.Curvature.LocalIsometryInvariants











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.M47



theorem localResult_scalar_eq
    {g₀ : StandardInitialMetric} {K : MetricSurgeryConstants}
    {P : SurgeryParameters} {slice : ℝ → GeneralizedSliceCarrier.{u}}
    {metric : ∀ t, RiemannianMetric 3 (slice t).carrier} {T : ℝ}
    (E : SurgeryEventData g₀ K P slice metric T) (D : LeviCivitaData (metric T))
    (i : Fin E.cap_count) (y : (E.local_result i).output.carrier) :
    (E.local_result i).connection.scalarCurvature y = D.scalarCurvature (E.local_embed i y) :=
  (E.local_result i).connection.scalarCurvature_eq_of_local_isometry D isOpen_univ
    (E.local_embed_smooth i).contMDiffOn
    (fun z _ v w => (E.local_metric i z v w).symm) (mem_univ y)




theorem exists_component_cap_exclusion_cutoff
    (g₀ : StandardInitialMetric) (K : MetricSurgeryConstants) (Db : ℝ) (hDb : 0 < Db) :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ (P : SurgeryParameters) (slice : ℝ → GeneralizedSliceCarrier.{u})
        (metric : ∀ t, RiemannianMetric 3 (slice t).carrier) (T : ℝ)
        (E : SurgeryEventData g₀ K P slice metric T) (D : LeviCivitaData (metric T)),
        P.delta T ≤ delta → ∀ H : ℝ, 0 < H → ∀ x : (slice T).carrier,
        (∀ z ∈ connectedComponent x, D.scalarCurvature z ≤ H) →
        intrinsicDiameter (metric T) (connectedComponent x) <
          ENNReal.ofReal (Db / Real.sqrt H) →
        ∀ i, Disjoint (connectedComponent x) (E.caps i).carrier := by
  obtain ⟨eta₀, heta₀, _heta₀small, htip⟩ := exists_tip_scalar_accuracy.{u} g₀
  let rho := 4 * (Db + 1)
  have hrho : 0 < rho := by dsimp only [rho]; positivity
  let eta := min eta₀ (min (1 / 2 : ℝ) (1 / (rho + 1)))
  have heta : 0 < eta := lt_min heta₀ (lt_min (by norm_num) (by positivity))
  have hetaTip : eta ≤ eta₀ := min_le_left _ _
  have hetaHalf : eta ≤ 1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hetaBuffer : eta ≤ 1 / (rho + 1) := (min_le_right _ _).trans (min_le_right _ _)
  have hbuffer : rho < eta⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ heta]
    have he := (le_div_iff₀ (by positivity : 0 < rho + 1)).mp hetaBuffer
    nlinarith
  refine ⟨K.comparison_delta eta, K.comparison_delta_pos eta heta, ?_⟩
  intro P slice metric T E D hdelta H hH x hupper hdiam i
  apply Set.disjoint_left.mpr
  intro y hy hcap
  have htipComponent : (E.caps i).tip ∈ connectedComponent x := by
    have hytip := cap_subset_tip_component E i hcap
    have heq : connectedComponent x = connectedComponent (E.caps i).tip :=
      (connectedComponent_eq hy).trans (connectedComponent_eq hytip).symm
    rw [heq]
    exact mem_connectedComponent
  obtain ⟨Q⟩ := (E.local_result i).standard_close eta heta
    (by simpa only [E.neck_delta i] using hdelta)
  have htipLower := htip (E.local_result i).output (E.local_result i).metric
    (E.local_result i).connection (E.local_result i).tip (E.necks i).neck.scale eta Q hetaTip
  have hlocalTip := localResult_scalar_eq E D i (E.local_result i).tip
  rw [E.local_tip i] at hlocalTip
  have htipUpper : (E.local_result i).connection.scalarCurvature (E.local_result i).tip ≤ H :=
    hlocalTip.trans_le (hupper (E.caps i).tip htipComponent)
  let h := (E.necks i).neck.scale
  have hh : 0 < h := Q.scale_pos
  have hscaled : (3 / 4 : ℝ) < h ^ 2 * H :=
    htipLower.trans_le (mul_le_mul_of_nonneg_left htipUpper (sq_nonneg h))
  have hsqrt : 0 < Real.sqrt H := Real.sqrt_pos.mpr hH
  have hsquare : (h * Real.sqrt H) ^ 2 = h ^ 2 * H := by
    rw [mul_pow, Real.sq_sqrt hH.le]
  have hhlow : (1 / 2 : ℝ) < h * Real.sqrt H := by
    have hpos := mul_pos hh hsqrt
    nlinarith
  have hradical : h / 2 ≤ Real.sqrt (h ^ 2 * (1 - eta)) := by
    apply (Real.le_sqrt (by positivity)
      (mul_nonneg (sq_nonneg h) (by linarith : 0 ≤ 1 - eta))).mpr
    nlinarith [sq_nonneg h]
  have hproduct : Db < Real.sqrt (h ^ 2 * (1 - eta)) * rho * Real.sqrt H := by
    have hlarge := mul_lt_mul_of_pos_right hhlow (half_pos hrho)
    have hcompare := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hradical hrho.le) hsqrt.le
    dsimp only [rho] at hlarge
    nlinarith
  have hradius : Db / Real.sqrt H ≤ Real.sqrt (h ^ 2 * (1 - eta)) * rho :=
    ((div_lt_iff₀ hsqrt).mpr hproduct).le
  have hdisjoint := component_disjoint_cap_of_comparison E i x Q
    (by linarith) hrho hbuffer
    (hdiam.trans_le (ENNReal.ofReal_le_ofReal hradius))
  exact Set.disjoint_left.mp hdisjoint hy hcap

end PoincareConjecture.M47
