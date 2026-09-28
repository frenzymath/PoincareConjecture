import PoincareConjecture.Proofs.M47.SeedTube
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarBound
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Claim16_27_CylinderMetricComparison

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle

universe u

namespace PoincareConjecture.Proofs.M47

theorem seed_search_scalar_and_curvature
    (P : M47Predecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    (p : SurgeryParameterPrefix S.constants) (compatible : S.SeedCompatible p)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    (old : SurgeryPrefixControls p F O) (hpinch : SurgeryFlowPinched F)
    {origin c H B : ℝ} {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hc : c ≤ 0) (hH : 0 < H) (hlevel : (p.r (Fin.last p.i))⁻¹ ^ 2 ≤ H)
    (hB : M46.seedAnalyticConstant S ≤ B)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hinitial : ∀ x ∈ U, (F.connection origin).scalarCurvature x ≤ 2 * H)
    (hold : ∀ s ∈ Ioo c 0,
      origin + s / 1 ∈ surgeryObservationInterval O ∩ prefixFinalInterval p)
    (hancestor : ∀ s (hs : s ∈ Ioo c 0), ∀ x ∈ U,
      ¬ SurgeryPositiveComponentAt F (origin + s / 1)
        (e.forward s (Ioo_subset_Icc_self hs) x))
    (hshort : 64 * B * H * (-c) ≤ 1) :
    ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x) ≤ 4 * H ∧
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤
        13 * max (4 * H) (Real.exp 4) := by
  let P44 : M44CapPersistencePredecessors.{u} := ⟨P.m04, P.m13.ordinary_flow⟩
  let r := (Real.sqrt H)⁻¹
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hH)
  have hrH : r⁻¹ ^ 2 = H := by
    dsimp only [r]
    rw [inv_inv, Real.sq_sqrt hH.le]
  have hBpos : 0 < B := (M46.seedAnalyticConstant_pos S).trans_le hB
  have hzero : 0 ∈ Icc c 0 := ⟨hc, le_rfl⟩
  have hline (x : (F.slice origin).carrier) (hx : x ∈ U) :
      ∀ s ∈ Icc c 0, M46.cylinderScalar e x s ≤ 4 * H := by
    have hstart : M46.cylinderScalar e x 0 ≤ 2 * r⁻¹ ^ 2 := by
      rw [M46.cylinderScalar_of_mem e x 0 hzero, hrH]
      have hp : (⟨origin + 0 / 1, e.forward 0 hzero x⟩ :
          (t : ℝ) × (F.slice t).carrier) = ⟨origin, x⟩ := by
        apply Sigma.ext (by simp)
        exact hbase hzero x hx
      have heq := congrArg (fun q : (t : ℝ) × (F.slice t).carrier =>
        (F.connection q.1).scalarCurvature q.2) hp
      exact heq ▸ hinitial x hx
    have hrate : ∀ s ∈ Ioo c 0, origin + s / 1 ∉ F.surgery_times →
        r⁻¹ ^ 2 ≤ M46.cylinderScalar e x s →
          |M46.cylinderScalarRate e x s| ≤ B * M46.cylinderScalar e x s ^ 2 := by
      intro s hs _hregular hhigh
      have hhigh' : H ≤ (F.connection (origin + s / 1)).scalarCurvature
          (e.forward s (Ioo_subset_Icc_self hs) x) := by
        simpa only [hrH, M46.cylinderScalar_of_mem e x s (Ioo_subset_Icc_self hs)] using hhigh
      have hcanon := old_prefix_seed_canonical S p compatible old (hold s hs)
        (e.forward s (Ioo_subset_Icc_self hs) x) (hlevel.trans hhigh')
      have hanalytic := M46.canonical_analytic_on_nonpositive S F (origin + s / 1)
        (e.forward s (Ioo_subset_Icc_self hs) x) hcanon (hancestor s hs x hx)
      classical
      simpa only [M46.cylinderScalar, M46.cylinderScalarRate,
        dif_pos (Ioo_subset_Icc_self hs)] using
        hanalytic.2.2.trans (mul_le_mul_of_nonneg_right hB (sq_nonneg _))
    have h := M46.cylinderScalar_le_four_inv_sq P44 hpinch e hx hc hBpos hr
      hstart hrate (by simpa only [hrH] using hshort)
    simpa only [hrH] using h
  intro s hs x hx
  have hscalar : (F.connection (origin + s / 1)).scalarCurvature
      (e.forward s hs x) ≤ 4 * H := by
    simpa only [M46.cylinderScalar_of_mem e x s hs] using hline x hx s hs
  have ht := e.time_subset (mem_image_of_mem _ hs)
  exact ⟨hscalar, (M46.pinched_curvature_norm_le P.toM46 (hpinch _ ht)
    (mem_univ (e.forward s hs x))).trans
      (mul_le_mul_of_nonneg_left (max_le_max_right _ hscalar) (by norm_num))⟩

theorem seed_search_metric_comparison
    (P : M47Predecessors.{u}) {F : SurgeryFlowData.{u}}
    (hpinch : SurgeryFlowPinched F) {origin c K : ℝ}
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
    (hU : IsOpen U) (hK : 0 ≤ K)
    (hbase : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
    (hRm : ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U,
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤ K)
    (hshort : 6 * K * (-c) ≤ 1 / 2) :
    ∀ s (hs : s ∈ Icc c 0), ∀ x ∈ U, ∀ v : TangentSpace (𝓡 3) x,
      (F.metric origin).inner x v v ≤
          2 * (F.metric (origin + s / 1)).inner (e.forward s hs x)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ∧
        (F.metric (origin + s / 1)).inner (e.forward s hs x)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v)
            (mfderiv (𝓡 3) (𝓡 3) (e.forward s hs) x v) ≤
          2 * (F.metric origin).inner x v v := by
  intro s hs x hx v
  apply M46.based_cylinder_metric_comparison_two ⟨P.m04, P.m13.ordinary_flow⟩
    hpinch e hU hbase hx v hs ?_ (fun t ht => hRm t ht x hx)
  exact (mul_le_mul_of_nonneg_left (neg_le_neg hs.1) (mul_nonneg (by norm_num) hK)).trans hshort

end PoincareConjecture.Proofs.M47
