import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedSupport.LongSectorTemplates

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

theorem saddle_nested_raised_return_radial_avoidance
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
    let path : ℝ → E2 := fun t =>
      kappa (J2.symm (0, raisedReturnSign inner * (1 + 10 * h - t)))
    ContinuousAt path 0 ∧ path 0 = gamma (1 / 2) ∧
      IsPreconnected (path '' Ioc (0 : ℝ) (10 * h)) ∧
      Disjoint (path '' Ioc (0 : ℝ) (10 * h))
        (gamma '' Icc (0 : ℝ) 1) ∧
      path (10 * h) = kappa (J2.symm (0, raisedReturnSign inner)) := by
  let g : ℝ → E2 := raisedReturnPlanarCurve J2 h inner
  let gamma : ℝ → E2 := raisedReturnPhysicalCurve kappa J2 h inner
  let radial : ℝ → E2 := fun t =>
    J2.symm (0, raisedReturnSign inner * (1 + 10 * h - t))
  let path : ℝ → E2 := fun t => kappa (radial t)
  change ContinuousAt path 0 ∧ path 0 = gamma (1 / 2) ∧
    IsPreconnected (path '' Ioc (0 : ℝ) (10 * h)) ∧
    Disjoint (path '' Ioc (0 : ℝ) (10 * h)) (gamma '' Icc (0 : ℝ) 1) ∧
    path (10 * h) = kappa (J2.symm (0, raisedReturnSign inner))
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source :=
    hkappaSource (by simpa only [mem_closedBall_zero_iff] using hx)
  have hradialNorm (t : ℝ) (ht : t ≤ 10 * h) :
      ‖radial t‖ = 1 + 10 * h - t := by
    have hn := hJ2 (radial t)
    simp only [radial, J2.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, mul_pow, raisedReturnSign_sq, one_mul] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) (by linarith : 0 ≤ 1 + 10 * h - t)).mp hn.symm
  have hradialSource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (10 * h)) :
      radial t ∈ kappa.source := by
    apply hsrc
    rw [hradialNorm t ht.2]
    linarith [ht.1]
  have hradialContinuous : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hAt : ContinuousAt path 0 :=
    (kappa.continuousAt (hradialSource 0 ⟨le_rfl, by linarith⟩)).comp
      hradialContinuous.continuousAt
  have hOn : ContinuousOn path (Ioc (0 : ℝ) (10 * h)) :=
    kappa.continuousOn.comp hradialContinuous.continuousOn
      (fun t ht => hradialSource t ⟨ht.1.le, ht.2⟩)
  have hmid : path 0 = gamma (1 / 2) := by
    dsimp only [path, radial, gamma, raisedReturnPhysicalCurve]
    rw [raisedReturn_mid_formula h hh hsmall J2 inner, sub_zero]
  have hnorm (t : ℝ) : ‖g t‖ = raisedReturnRadius h t :=
    raisedReturnPlanar_norm_eq_radius J2 hJ2 h inner t
      (raisedReturnRadius_nonneg h hh t)
  have hcurveSource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : g t ∈ kappa.source := by
    apply hsrc
    rw [hnorm t]
    have hbound := raisedReturnRadius_upper_closed h hh hsmall t ht
    linarith
  have hdisjoint : Disjoint (path '' Ioc (0 : ℝ) (10 * h))
      (gamma '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    have hxy : g t = radial s :=
      kappa.injOn (hcurveSource t ht) (hradialSource s ⟨hs.1.le, hs.2⟩) heq
    have hsector : |(J2 (g t)).1| ≤
        raisedReturnSign inner * (J2 (g t)).2 := by
      rw [hxy]
      simp only [radial, J2.apply_symm_apply, abs_zero, ← mul_assoc,
        ← pow_two, raisedReturnSign_sq, one_mul]
      linarith [hs.2]
    have hq := raisedReturn_opposite_sector_q J2 h hh hsmall inner t ht hsector
    have hbound := raisedReturn_radius_lower_of_opposite_sector h hh t hq
    have hR : raisedReturnRadius h t = 1 + 10 * h - s := by
      rw [← hnorm t, hxy, hradialNorm s hs.2]
    linarith [hs.1]
  refine ⟨hAt, hmid, isPreconnected_Ioc.image path hOn, hdisjoint, ?_⟩
  simp [path, radial]

end PoincareConjecture.M25.Topology3D
