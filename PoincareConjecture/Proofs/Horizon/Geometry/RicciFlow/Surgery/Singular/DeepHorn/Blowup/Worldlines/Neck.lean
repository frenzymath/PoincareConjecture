import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Blowup.Worldlines
import PoincareConjecture.Proofs.Horizon.Geometry.RicciFlow.Surgery.Singular.DeepHorn.Neck.Restriction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set
open scoped Manifold ContDiff Bundle ENNReal Topology

universe u

namespace PoincareConjecture.GeneralizedStrongNeck

theorem maximalBackwardFlowLine {F : GeneralizedRicciFlowData.{u}}
    {t epsilon : ℝ} (N : GeneralizedStrongNeck F t epsilon)
    {q mu : ℝ} (hq : 0 < q) (_hmu : 0 < mu) (hmu1 : mu < 1) :
    Nonempty (GeneralizedMaximalBackwardFlowLine F ⟨t, N.center⟩ q
      (mu * q / max q ((F.connection t).scalarCurvature N.center))) := by
  let R := (F.connection t).scalarCurvature N.center
  have hR : 0 < R := N.scalar_center_pos
  have hscale : N.scale = (Real.sqrt R)⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  have hr : N.scale⁻¹ ^ 2 = R := by
    rw [hscale, inv_inv, Real.sq_sqrt hR.le]
  let e := N.time_cylinder.restrictSpace
    (singleton_subset_iff.mpr (N.central_sphere_subset N.center_on_central_sphere))
  apply DeepHorn.maximalBackwardFlowLine_of_rescaled_cylinder e ordConnected_Ioc
    (show (0 : ℝ) ∈ Ioc (-1) 0 by norm_num)
    (N.cylinder_identity _ _ (N.central_sphere_subset N.center_on_central_sphere)) hq
  intro s hs
  rw [hr]
  have hm : 0 < max q R := lt_of_lt_of_le hq (le_max_left _ _)
  have hduration : (mu * q / max q R) * R < q := by
    have hmul : mu * R < max q R :=
      (mul_lt_of_lt_one_left hR hmu1).trans_le (le_max_right _ _)
    calc
      (mu * q / max q R) * R = (mu * R / max q R) * q := by ring
      _ < 1 * q := mul_lt_mul_of_pos_right ((div_lt_iff₀ hm).mpr (by simpa using hmul)) hq
      _ = q := one_mul q
  refine ⟨(lt_div_iff₀ hq).mpr ?_, div_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonpos_of_nonneg hs.2 hR.le) hq.le⟩
  have hlow := mul_le_mul_of_nonneg_right hs.1 hR.le
  dsimp only [R] at hduration hlow ⊢
  linarith

end PoincareConjecture.GeneralizedStrongNeck

namespace PoincareConjecture.DeepHorn

theorem maximalBackwardFlowLine_contains_neck_interval
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {q duration epsilon s : ℝ}
    (L : GeneralizedMaximalBackwardFlowLine F p q duration)
    (hs : s ∈ interior L.maximal_interval)
    (N : GeneralizedStrongNeck F (p.1 + s / q) epsilon)
    (hcenter : N.center = L.embedding.forward s (interior_subset hs) p.2) :
    Ioc (s - q / ((F.connection (p.1 + s / q)).scalarCurvature N.center)) s ⊆
      L.maximal_interval := by
  let R := (F.connection (p.1 + s / q)).scalarCurvature N.center
  have hR : 0 < R := N.scalar_center_pos
  have hq : 0 < q := L.embedding.scale_pos
  have hscale : N.scale = (Real.sqrt R)⁻¹ := by
    rw [N.scale_scalar, neg_div, Real.rpow_neg N.scalar_center_pos.le, Real.sqrt_eq_rpow]
  have hr : N.scale⁻¹ ^ 2 = R := by
    rw [hscale, inv_inv, Real.sq_sqrt hR.le]
  let e := N.time_cylinder.restrictSpace
    (singleton_subset_iff.mpr (N.central_sphere_subset N.center_on_central_sphere))
  obtain ⟨e', he'⟩ := exists_rebased_singleton_cylinder
    (p := p) (p' := ⟨p.1 + s / q, N.center⟩) (a := s) e ordConnected_Ioc hq rfl
  let I := (fun t : ℝ => (t - s) * N.scale⁻¹ ^ 2 / q) ⁻¹' Ioc (-1) 0
  have hI : I = Ioc (s - q / R) s := by
    ext t
    simp only [I, mem_preimage, mem_Ioc, hr]
    rw [lt_div_iff₀ hq, div_le_iff₀ hq]
    have hQR : q / R * R = q := div_mul_cancel₀ q (ne_of_gt hR)
    constructor
    · rintro ⟨hl, hu⟩
      constructor <;> nlinarith
    · rintro ⟨hl, hu⟩
      constructor <;> nlinarith
  have hsI : s ∈ I := by rw [hI]; exact ⟨sub_lt_self s (div_pos hq hR), le_rfl⟩
  have hinter : (interior L.maximal_interval ∩ interior I).Nonempty := by
    obtain ⟨delta, hd, hball⟩ := Metric.mem_nhds_iff.mp (isOpen_interior.mem_nhds hs)
    let d := min delta (q / R)
    have hdpos : 0 < d := lt_min hd (div_pos hq hR)
    have hdleft : d ≤ delta := min_le_left _ _
    have hdright : d ≤ q / R := min_le_right _ _
    refine ⟨s - d / 2, hball ?_, ?_⟩
    · rw [Metric.mem_ball, Real.dist_eq, abs_of_nonpos (by linarith : s - d / 2 - s ≤ 0)]
      linarith
    · rw [hI, interior_Ioc]
      exact ⟨by linarith, by linarith⟩
  have hmeet : L.embedding.pointMap s (interior_subset hs) p.2 = e'.pointMap s hsI p.2 := by
    rw [he']
    have hid := N.cylinder_identity (show (0 : ℝ) ∈ Ioc (-1) 0 by norm_num) N.center
      (N.central_sphere_subset N.center_on_central_sphere)
    have hepoint : e.pointMap ((s - s) * N.scale⁻¹ ^ 2 / q) hsI N.center =
        (⟨p.1 + s / q, N.center⟩ : F.point) := by
      have hezero (a : ℝ) (ha : a ∈ Ioc (-1) 0) (ha0 : a = 0) :
          e.pointMap a ha N.center = (⟨p.1 + s / q, N.center⟩ : F.point) := by
        subst a
        exact hid
      exact hezero _ hsI (by ring)
    exact (congrArg (Sigma.mk (p.1 + s / q)) hcenter.symm).trans hepoint.symm
  rw [← hI]
  exact maximalBackwardFlowLine_contains_overlapping_cylinder L e'
    (hI ▸ ordConnected_Ioc) hinter (interior_subset hs) hsI hmeet

theorem maximalBackwardFlowLine_contains_interval_of_bounded_necks
    {F : GeneralizedRicciFlowData.{u}} {p : F.point} {q duration epsilon T B : ℝ}
    (L : GeneralizedMaximalBackwardFlowLine F p q duration)
    (hduration : 0 < duration) (hB : 0 < B)
    (hnecks : ∀ s (hs : s ∈ interior L.maximal_interval), -T < s → s < 0 →
      ∃ N : GeneralizedStrongNeck F (p.1 + s / q) epsilon,
        N.center = L.embedding.forward s (interior_subset hs) p.2 ∧
        (F.connection (p.1 + s / q)).scalarCurvature N.center ≤ B) :
    Icc (-T) 0 ⊆ L.maximal_interval := by
  have hq : 0 < q := L.embedding.scale_pos
  apply interval_contains_of_uniform_backward_extension L.maximal_interval_ordConnected
    L.maximal_interval_mem_zero
    ⟨-duration, L.requested_interval_subset ⟨le_rfl, neg_nonpos.mpr hduration.le⟩,
      neg_neg_of_pos hduration⟩ (div_pos hq hB)
  intro s hs hsT hs0
  obtain ⟨N, hcenter, hbound⟩ := hnecks s hs hsT hs0
  have htime : q / B ≤ q / ((F.connection (p.1 + s / q)).scalarCurvature N.center) :=
    div_le_div_of_nonneg_left hq.le N.scalar_center_pos hbound
  exact (Ioc_subset_Ioc_left (sub_le_sub_left htime s)).trans
    (maximalBackwardFlowLine_contains_neck_interval L hs N hcenter)

theorem maximalBackwardFlowLineSurvival_of_strongNecks
    (S : GeneralizedBlowupSequence.{u}) {mu epsilon : ℝ}
    (hmu : 0 < mu) (hmu1 : mu < 1)
    (hnecks : ∀ A : ℝ, 0 < A → ∀ᶠ k : ℕ in Filter.atTop,
      ∀ x ∈ S.baseBall k A,
        ∃ N : GeneralizedStrongNeck (S.flow k) (S.base k).1 epsilon, N.center = x) :
    GeneralizedMaximalBackwardFlowLineSurvival S mu := by
  intro A hA
  filter_upwards [hnecks A hA] with k hk
  intro x hx
  obtain ⟨N, rfl⟩ := hk x hx
  exact N.maximalBackwardFlowLine (S.base_scalar_pos k) hmu hmu1

end PoincareConjecture.DeepHorn
