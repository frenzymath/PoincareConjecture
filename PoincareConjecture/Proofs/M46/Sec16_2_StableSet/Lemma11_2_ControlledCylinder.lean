import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_BackwardCylinderExistence
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_CylinderScalarBound
import PoincareConjecture.Proofs.M46.Sec16_2_StableSet.Lemma11_2_LowScalarRetained
import PoincareConjecture.Proofs.M44.Sec16_1_CapPersistence.Def_InitialCylinder
import PoincareConjecture.Proofs.M33.SurgeryCylinderRestriction











set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff

universe u

namespace PoincareConjecture.Proofs.M46




theorem exists_scalar_controlled_backward_cylinder
    (P : M44CapPersistencePredecessors.{u}) (S : RepairedControlledSchedulesData.{u})
    {F : SurgeryFlowData.{u}} (hpinch : SurgeryFlowPinched F)
    {origin duration B r : ℝ} (hduration : 0 ≤ duration)
    (hB : seedAnalyticConstant S ≤ B) (hr : 0 < r)
    (hshort : 64 * B * r⁻¹ ^ 2 * duration ≤ 1)
    (htime : Icc (origin - duration) origin ⊆ F.time_domain)
    (hfuture : ∃ top : ℝ, origin < top ∧ top ∈ F.time_domain)
    (U : Set (F.slice origin).carrier) (hU : IsOpen U) (hne : U.Nonempty)
    (hscalar : ∀ x ∈ U, (F.connection origin).scalarCurvature x ≤ 2 * r⁻¹ ^ 2)
    (hpositive : ∀ x ∈ U, ¬ SurgeryPositiveComponentAt F origin x)
    (hcanonical : ∀ t ∈ Icc (origin - duration) origin,
      ∀ x : (F.slice t).carrier, r⁻¹ ^ 2 ≤ (F.connection t).scalarCurvature x →
        SurgeryCanonicalControl F t x F.parameters.epsilon S.setup.C)
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
  have hBpos : 0 < B := (seedAnalyticConstant_pos S).trans_le hB
  have hcoefficient : 0 ≤ 64 * B * r⁻¹ ^ 2 := by positivity
  have hcontrol (c : ℝ) (hc : c ∈ Icc (-duration) 0)
      (e : SurgeryFlowCylinder F (F.slice origin) origin 1 (Icc c 0) U)
      (he : ∀ h x, x ∈ U → HEq (e.forward 0 h x) x)
      (x : (F.slice origin).carrier) (hx : x ∈ U) :
      ∀ s ∈ Icc c 0, cylinderScalar e x s ≤ 4 * r⁻¹ ^ 2 := by
    have hpoint : (⟨origin + 0 / 1, e.forward 0 ⟨hc.2, le_rfl⟩ x⟩ :
        (t : ℝ) × (F.slice t).carrier) = ⟨origin, x⟩ :=
      Sigma.ext (by simp) (he _ x hx)
    have hzero := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
      (F.connection p.1).scalarCurvature p.2) hpoint
    have hnonpositive : ¬ SurgeryPositiveComponentAt F (origin + 0 / 1)
        (e.forward 0 ⟨hc.2, le_rfl⟩ x) := by
      have hp := congrArg (fun p : (t : ℝ) × (F.slice t).carrier =>
        SurgeryPositiveComponentAt F p.1 p.2) hpoint
      rw [hp]
      exact hpositive x hx
    apply canonical_cylinderScalar_le_four_inv_sq P S hpinch e hx hc.2 hB hr
      hnonpositive _ _ _
    · rw [cylinderScalar_of_mem e x 0 ⟨hc.2, le_rfl⟩, hzero]
      exact hscalar x hx
    · intro s hs _ hhigh
      apply hcanonical (origin + s / 1)
        (by simp only [div_one]; constructor <;> linarith [hc.1, hs.1, hs.2])
      simpa only [cylinderScalar_of_mem e x s (Ioo_subset_Icc_self hs)] using hhigh
    · exact (mul_le_mul_of_nonneg_left (by linarith only [hc.1] : -c ≤ duration)
        hcoefficient).trans hshort
  obtain ⟨top, htop, htopmem⟩ := hfuture
  have horigin : origin ∈ F.time_domain := htime ⟨by linarith, le_rfl⟩
  have hfutureTime : ∀ s ∈ Ico 0 (top - origin), origin + s / 1 ∈ F.time_domain := by
    intro s hs
    apply F.time_domain_interval.out horigin htopmem
    simp only [div_one]
    constructor <;> linarith [hs.1, hs.2]
  obtain ⟨c, hc, _hcTop, initial, hinitial⟩ :=
    M44.exists_initial_based_cylinder F zero_lt_one (sub_pos.mpr htop) hfutureTime U
  have hzeroSubset : Icc (0 : ℝ) 0 ⊆ Ico 0 c := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt hc⟩
  let initialZero := initial.restrict hzeroSubset ordConnected_Icc (Subset.refl U)
  obtain ⟨e, he⟩ := exists_backward_cylinder_of_retained_frontiers P hpinch
    (neg_nonpos.mpr hduration) (by simpa only [sub_eq_add_neg] using htime)
    U hU hne initialZero (fun h x hx => hinitial _ x hx) (by
      intro c hc e he hT _
      rintro _ ⟨x, hx, rfl⟩
      apply low_scalar_subset_retained_interior F hT
        (hcap (origin + c / 1)
          (by simp only [div_one]; constructor <;> linarith [hc.1, hc.2]) hT)
      have h := hcontrol c ⟨hc.1.le, hc.2⟩ e he x hx c ⟨le_rfl, hc.2⟩
      simpa only [mem_ofPred_eq, cylinderScalar_of_mem e x c ⟨le_rfl, hc.2⟩] using h)
  refine ⟨e, he, ?_⟩
  intro s hs x hx
  have h := hcontrol (-duration) ⟨le_rfl, neg_nonpos.mpr hduration⟩ e he x hx s hs
  simpa only [cylinderScalar_of_mem e x s hs] using h

end PoincareConjecture.Proofs.M46
