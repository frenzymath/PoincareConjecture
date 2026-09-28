import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.ShortSectorTemplates

set_option autoImplicit false

open Set Metric Function
open scoped ContDiff Topology

namespace PoincareConjecture.M25.Topology3D

set_option maxHeartbeats 600000 in

theorem saddle_nested_short_return_radial_approach
    (kappa : OpenPartialHomeomorph E2 E2)
    (hkappaSource : closedBall (0 : E2) 2 ⊆ kappa.source)
    (J2 : E2 ≃L[ℝ] (ℝ × ℝ))
    (hJ2 : ∀ x : E2, (J2 x).1 ^ 2 + (J2 x).2 ^ 2 = ‖x‖ ^ 2)
    (h : ℝ) (hh : 0 < h) (hsmall : h < 1 / 1024) (inner : Fin 2) :
    let sign : Fin 2 → ℝ := ![1, -1]
    let sx : Fin 4 → ℝ := ![1, -1, -1, 1]
    let sy : Fin 4 → ℝ := ![1, 1, -1, -1]
    let port : Fin 4 → E2 := fun a =>
      J2.symm (sx a / Real.sqrt 2, sy a / Real.sqrt 2)
    let ep : Fin 2 × Fin 2 ≃ Fin 4 := finProdFinEquiv
    let path : ℝ → E2 := fun t =>
      kappa (J2.symm (0, sign inner * (1 + h - t)))
    ∀ (alpha : Fin 2 → ℝ → E2) (b g : ℝ → E2),
      (∀ t ∈ Icc (3 * h) (1 - 3 * h),
        1 + 3 * h ≤ ‖b t‖ ∧ ‖b t‖ ≤ 1 + 6 * h) →
      (∀ t ∈ Icc (0 : ℝ) 1,
        1 + h ≤ ‖g t‖ ∧ ‖g t‖ ≤ 1 + 3 * h) →
      kappa (g (1 / 2)) = kappa (J2.symm (0, sign inner * (1 + h))) →
      (∀ j, (alpha j '' Icc (0 : ℝ) 1) ∩
          (kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h}) =
        kappa ''
          (((fun r : ℝ => r • port (ep (inner, 0))) '' Icc 1 (1 + 32 * h)) ∪
          ((fun r : ℝ => r • port (ep (inner, 1))) '' Icc 1 (1 + 32 * h)))) →
      ContinuousAt path 0 ∧ path 0 = kappa (g (1 / 2)) ∧
        IsPreconnected (path '' Ioc (0 : ℝ) h) ∧
        Disjoint (path '' Ioc (0 : ℝ) h) ((kappa ∘ g) '' Icc (0 : ℝ) 1) ∧
        Disjoint (path '' Ioc (0 : ℝ) h)
          ((kappa ∘ b) '' Icc (3 * h) (1 - 3 * h)) ∧
        (∀ j, Disjoint (path '' Ioc (0 : ℝ) h) (alpha j '' Icc (0 : ℝ) 1)) ∧
        path h = kappa (J2.symm (0, sign inner)) ∧
        path h ∈ kappa '' closedBall (0 : E2) 1 := by
  intro sign sx sy port ep path alpha b g hb hg hMid hAnnular
  let radial : ℝ → E2 := fun t => J2.symm (0, sign inner * (1 + h - t))
  have hsign (i : Fin 2) : (sign i) ^ 2 = 1 := by
    fin_cases i <;> norm_num [sign]
  have hsrc {x : E2} (hx : ‖x‖ ≤ 2) : x ∈ kappa.source :=
    hkappaSource (mem_closedBall_zero_iff.mpr hx)
  have hnorm (t : ℝ) (ht : t ≤ h) : ‖radial t‖ = 1 + h - t := by
    have hn := hJ2 (radial t)
    simp only [radial, J2.apply_symm_apply, zero_pow (by norm_num : 2 ≠ 0),
      zero_add, mul_pow, hsign, one_mul] at hn
    exact (sq_eq_sq₀ (norm_nonneg _) (by linarith : 0 ≤ 1 + h - t)).mp hn.symm
  have hsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) h) : radial t ∈ kappa.source := by
    apply hsrc
    rw [hnorm t ht.2]
    linarith [ht.1]
  have hcontinuous : Continuous radial := by
    dsimp [radial]
    fun_prop
  have hAt : ContinuousAt path 0 :=
    (kappa.continuousAt (hsource 0 ⟨le_rfl, hh.le⟩)).comp hcontinuous.continuousAt
  have hOn : ContinuousOn path (Ioc (0 : ℝ) h) :=
    kappa.continuousOn.comp hcontinuous.continuousOn
      (fun t ht => hsource t ⟨ht.1.le, ht.2⟩)
  have hpathMid : path 0 = kappa (g (1 / 2)) := by
    simpa only [path, sub_zero] using hMid.symm
  have hGamma : Disjoint (path '' Ioc (0 : ℝ) h)
      ((kappa ∘ g) '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    have hgs : g t ∈ kappa.source := hsrc (by linarith [(hg t ht).2])
    have he : g t = radial s := kappa.injOn hgs (hsource s ⟨hs.1.le, hs.2⟩) heq
    have hlo := (hg t ht).1
    rw [he, hnorm s hs.2] at hlo
    linarith [hs.1]
  have hBeta : Disjoint (path '' Ioc (0 : ℝ) h)
      ((kappa ∘ b) '' Icc (3 * h) (1 - 3 * h)) := by
    apply disjoint_left.mpr
    rintro y ⟨s, hs, rfl⟩ ⟨t, ht, heq⟩
    have hbs : b t ∈ kappa.source := hsrc (by linarith [(hb t ht).2])
    have he : b t = radial s := kappa.injOn hbs (hsource s ⟨hs.1.le, hs.2⟩) heq
    have hlo := (hb t ht).1
    rw [he, hnorm s hs.2] at hlo
    linarith [hs.1]
  have hportN (a : Fin 4) : ‖port a‖ = 1 := by
    have hn := hJ2 (port a)
    have hs : (sx a) ^ 2 = 1 ∧ (sy a) ^ 2 = 1 := by
      fin_cases a <;> norm_num [sx, sy]
    simp only [port, J2.apply_symm_apply, div_pow, hs.1, hs.2,
      Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] at hn
    nlinarith [norm_nonneg (port a)]
  have hportCone (i e : Fin 2) (r : ℝ) (hr : 0 ≤ r) :
      |(J2 (r • port (ep (i, e)))).1| = sign i * (J2 (r • port (ep (i, e)))).2 := by
    have hsq := Real.sqrt_nonneg (2 : ℝ)
    fin_cases i <;> fin_cases e <;>
      simp [port, ep, finProdFinEquiv, sx, sy, sign, map_smul,
        abs_mul, abs_div, abs_of_nonneg hr, abs_of_nonneg hsq] <;> ring
  have hAlpha (j : Fin 2) :
      Disjoint (path '' Ioc (0 : ℝ) h) (alpha j '' Icc (0 : ℝ) 1) := by
    apply disjoint_left.mpr
    rintro y ⟨t, ht, rfl⟩ hyAlpha
    have hyAnn : path t ∈
        kappa '' {x : E2 | 1 ≤ ‖x‖ ∧ ‖x‖ ≤ 1 + 32 * h} := by
      refine ⟨radial t, ⟨?_, ?_⟩, rfl⟩ <;>
        rw [hnorm t ht.2] <;> linarith [ht.1, ht.2]
    have hyRay : path t ∈ kappa ''
        (((fun r : ℝ => r • port (ep (inner, 0))) '' Icc 1 (1 + 32 * h)) ∪
        ((fun r : ℝ => r • port (ep (inner, 1))) '' Icc 1 (1 + 32 * h))) := by
      rw [← hAnnular j]
      exact ⟨hyAlpha, hyAnn⟩
    have hRayFalse (e : Fin 2) (r : ℝ) (hr : r ∈ Icc 1 (1 + 32 * h))
        (he : kappa (r • port (ep (inner, e))) = path t) : False := by
      have hrN : ‖r • port (ep (inner, e))‖ = r := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by linarith [hr.1]),
          hportN, mul_one]
      have hrS : r • port (ep (inner, e)) ∈ kappa.source := hsrc (by
        rw [hrN]
        linarith [hr.2])
      have heq : r • port (ep (inner, e)) = radial t :=
        kappa.injOn hrS (hsource t ⟨ht.1.le, ht.2⟩) he
      have hcone := hportCone inner e r (by linarith [hr.1])
      rw [heq] at hcone
      simp only [radial, J2.apply_symm_apply, abs_zero, ← mul_assoc,
        ← pow_two, hsign, one_mul] at hcone
      linarith [ht.2]
    rcases hyRay with ⟨z, hz, hzImage⟩
    rcases hz with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩
    · exact hRayFalse 0 r hr hzImage
    · exact hRayFalse 1 r hr hzImage
  have hEnd : path h = kappa (J2.symm (0, sign inner)) := by simp [path]
  refine ⟨hAt, hpathMid, isPreconnected_Ioc.image path hOn, hGamma, hBeta,
    hAlpha, hEnd, ?_⟩
  refine ⟨radial h, mem_closedBall_zero_iff.mpr ?_, rfl⟩
  rw [hnorm h le_rfl]
  linarith

end PoincareConjecture.M25.Topology3D
