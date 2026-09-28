import PoincareConjecture.Proofs.M47.ComponentEstimateBackward
import PoincareConjecture.Proofs.M47.ComponentEstimateCylinder
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarBound
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_LowScalarRetained
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_SmallCurvature









set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.M47

open Proofs.M46



theorem exists_seed_low_scalar_cylinder
    (P : M44CapPersistencePredecessors.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {origin duration B r : ℝ} (hduration : 0 ≤ duration)
    (hB : 0 < B) (hr : 0 < r)
    (hshort : 64 * B * r⁻¹ ^ 2 * duration ≤ 1)
    (htime : Icc (origin - duration) origin ⊆ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U) (hne : U.Nonempty)
    (hscalar : ∀ x ∈ U, (F.connection origin).scalarCurvature x ≤ 2 * r⁻¹ ^ 2)
    (hrate : ∀ t ∈ Ioo (origin - duration) origin, t ∉ F.surgery_times →
      ∀ x : (F.slice t).carrier, r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
        |(F.connection t).laplacian (F.connection t).scalarCurvature x +
          2 * (F.connection t).ricciNormSq x| ≤ B * (F.connection t).scalarCurvature x ^ 2)
    (hcap : ∀ t ∈ Ioc (origin - duration) origin,
      ∀ (hT : t ∈ F.surgery_times) [Nonempty (F.slice t).carrier],
      ∀ i : Fin (F.event t hT).cap_count,
      ∀ x ∈ ((F.event t hT).caps i).carrier,
        4 * r⁻¹ ^ 2 < (F.connection t).scalarCurvature x) :
    ∃ e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (-duration) 0) U,
      (∀ h x, x ∈ U → HEq (e.forward 0 h x) x) ∧
      ∀ s hs x, x ∈ U →
        (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x) ≤
          4 * r⁻¹ ^ 2 := by
  classical
  have hcoefficient : 0 ≤ 64 * B * r⁻¹ ^ 2 := by positivity
  have hcontrol (c : ℝ) (hc : c ∈ Icc (-duration) 0)
      (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
      (he : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
      (x : (F.slice origin).carrier) (hx : x ∈ U) :
      ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * r⁻¹ ^ 2 := by
    have hpoint : (⟨origin + 0 / 1, e.forward 0 ⟨hc.2, le_rfl⟩ x⟩ :
        (t : ℝ) × (F.slice t).carrier) = ⟨origin, x⟩ :=
      Sigma.ext (by simp) (he _ x hx)
    have hzero := congrArg (fun q : (t : ℝ) × (F.slice t).carrier =>
      (F.connection q.1).scalarCurvature q.2) hpoint
    apply cylinderScalar_le_four_inv_sq P hpinch e hx hc.2 hB hr
    · rw [cylinderScalar_of_mem e x 0 ⟨hc.2, le_rfl⟩, hzero]
      exact hscalar x hx
    · intro s hs hnot hhigh
      have hstime : origin + s / 1 ∈ Ioo (origin - duration) origin := by
        simp only [div_one]
        constructor <;> linarith only [hc.1, hs.1, hs.2]
      have hR : r⁻¹ ^ 2 ≤ (F.connection (origin + s / 1)).scalarCurvature
          (e.forward s (Ioo_subset_Icc_self hs) x) := by
        simpa only [cylinderScalar_of_mem e x s (Ioo_subset_Icc_self hs)] using hhigh
      simpa only [cylinderScalar, cylinderScalarRate, dif_pos (Ioo_subset_Icc_self hs)]
        using hrate _ hstime hnot _ hR
    · exact (mul_le_mul_of_nonneg_left
        (by linarith only [hc.1] : -c ≤ duration) hcoefficient).trans hshort
  have horigin : origin ∈ F.time_domain := htime ⟨by linarith, le_rfl⟩
  obtain ⟨initial, hinitial⟩ := exists_component_singleton_cylinder F origin horigin U
  obtain ⟨e, he⟩ := exists_component_backward_cylinder_of_retained_frontiers
    (neg_nonpos.mpr hduration) (by simpa only [sub_eq_add_neg] using htime)
    U hU hne initial hinitial (by
      intro c hc e he hT _
      rintro _ ⟨x, hx, rfl⟩
      apply low_scalar_subset_retained_interior F hT
        (hcap (origin + c / 1)
          (by simp only [div_one]; constructor <;> linarith only [hc.1, hc.2]) hT)
      have h := hcontrol c ⟨hc.1.le, hc.2⟩ e he x hx c ⟨le_rfl, hc.2⟩
      simpa only [mem_ofPred_eq, cylinderScalar_of_mem e x c ⟨le_rfl, hc.2⟩] using h)
  refine ⟨e, he, ?_⟩
  intro s hs x hx
  have h := hcontrol (-duration) ⟨le_rfl, neg_nonpos.mpr hduration⟩ e he x hx s hs
  simpa only [cylinderScalar_of_mem e x s hs] using h



theorem seed_low_cylinder_curvature
    (P : M46Predecessors.{u}) {F : SurgeryFlowData.{u}}
    (hpinch : SurgeryFlowPinched F)
    {origin duration r : ℝ} (hr : 0 < r) (hrsmall : r ≤ 1 / 200)
    {U : Set (F.slice origin).carrier}
    (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc (-duration) 0) U)
    (hscalar : ∀ s hs x, x ∈ U →
      (F.connection (origin + s / 1)).scalarCurvature (e.forward s hs x) ≤
        4 * r⁻¹ ^ 2) :
    ∀ s hs x, x ∈ U →
      (F.connection (origin + s / 1)).curvatureTensorNorm (e.forward s hs x) ≤
        52 * r⁻¹ ^ 2 := by
  intro s hs x hx
  exact low_scalar_curvature_le_fifty_two P
    (hpinch _ (e.time_subset (mem_image_of_mem _ hs))) hr hrsmall _ (hscalar s hs x hx)

end PoincareConjecture.M47
