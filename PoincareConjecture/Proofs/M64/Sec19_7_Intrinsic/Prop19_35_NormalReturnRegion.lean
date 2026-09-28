import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Prop19_35_RegularLoop
import PoincareConjecture.Proofs.M64.Sec19_7_Intrinsic.Claim19_37_MeasurableNormalStrip

noncomputable section
set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace PoincareConjecture

theorem m64Intrinsic_regular_selfintersection_region
    {gamma : ℝ → AnnulusCoordinates} (hg : ContDiff ℝ ∞ gamma) {a b : ℝ}
    (hregular : ∀ s ∈ Icc a b, deriv gamma s ≠ 0)
    (hnot : ¬ InjOn gamma (Icc a b)) :
    ∃ s t : ℝ, a ≤ s ∧ s < t ∧ t ≤ b ∧ gamma s = gamma t ∧ InjOn gamma (Ico s t) ∧
      ∃ U V : Set AnnulusCoordinates,
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
        Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
        U ∪ V = (gamma '' Icc s t)ᶜ ∧
        frontier U = gamma '' Icc s t ∧ frontier V = gamma '' Icc s t ∧
        IsCompact (closure U) := by
  obtain ⟨s, t, has, hst, htb, heq, hinj⟩ :=
    m64Intrinsic_exists_simple_regular_loop hg hregular hnot
  let q : ℝ → AnnulusCoordinates := fun x => gamma (s + x)
  have hqc : Continuous q := hg.continuous.comp (continuous_const.add continuous_id)
  have hqe : q 0 = q (t - s) := by
    simpa only [q, add_zero, show s + (t - s) = t by ring] using heq
  have hqi : InjOn q (Ico 0 (t - s)) := by
    intro x hx y hy hxy
    have h := hinj (show s + x ∈ Ico s t from ⟨by linarith [hx.1], by linarith [hx.2]⟩)
      (show s + y ∈ Ico s t from ⟨by linarith [hy.1], by linarith [hy.2]⟩) hxy
    linarith
  have himage : q '' Icc 0 (t - s) = gamma '' Icc s t := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨s + x, ⟨by linarith [hx.1], by linarith [hx.2]⟩, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      refine ⟨x - s, ⟨by linarith [hx.1], by linarith [hx.2]⟩, ?_⟩
      change gamma (s + (x - s)) = gamma x
      congr 1
      ring
  obtain ⟨U, V, hU, hV, hpU, hpV, hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩ :=
    m64Intrinsic_exists_jordan_region (sub_pos.mpr hst) hqc.continuousOn hqe hqi
  rw [himage] at hunion hfU hfV
  exact ⟨s, t, has, hst, htb, heq, hinj, U, V, hU, hV, hpU, hpV,
    hbU, hbV, hdisj, hunion, hfU, hfV, hcompact⟩

theorem m64Intrinsic_normal_ray_deriv
    {u : ℝ × ℝ → AnnulusCoordinates} {a t : ℝ}
    (hu : DifferentiableAt ℝ u (a, t)) :
    deriv (fun s => u (a, s)) t = fderiv ℝ u (a, t) (0, 1) := by
  have hline : HasDerivAt (fun s : ℝ => (a, s)) (0, 1) t :=
    (hasDerivAt_const t a).prodMk (hasDerivAt_id t)
  exact (hu.hasFDerivAt.comp_hasDerivAt t hline).deriv

theorem m64Intrinsic_normal_selfintersection_region
    {u : ℝ × ℝ → AnnulusCoordinates} (hu : ContDiff ℝ ∞ u) {a b : ℝ}
    (hi : ∀ t ∈ Icc (0 : ℝ) b, Function.Injective (fderiv ℝ u (a, t)))
    (hnot : ¬ InjOn (fun t => u (a, t)) (Icc (0 : ℝ) b)) :
    ∃ s t : ℝ, 0 ≤ s ∧ s < t ∧ t ≤ b ∧ u (a, s) = u (a, t) ∧
      InjOn (fun x => u (a, x)) (Ico s t) ∧
      ∃ U V : Set AnnulusCoordinates,
        IsOpen U ∧ IsOpen V ∧ IsPathConnected U ∧ IsPathConnected V ∧
        Bornology.IsBounded U ∧ ¬ Bornology.IsBounded V ∧ Disjoint U V ∧
        U ∪ V = ((fun x => u (a, x)) '' Icc s t)ᶜ ∧
        frontier U = (fun x => u (a, x)) '' Icc s t ∧
        frontier V = (fun x => u (a, x)) '' Icc s t ∧
        IsCompact (closure U) := by
  have hq : ContDiff ℝ ∞ (fun t => u (a, t)) := hu.comp (by fun_prop)
  apply m64Intrinsic_regular_selfintersection_region hq _ hnot
  intro t ht hzero
  rw [m64Intrinsic_normal_ray_deriv (hu.differentiable (by simp) (a, t))] at hzero
  have h := hi t ht (hzero.trans (fderiv ℝ u (a, t)).map_zero.symm)
  have hlast := congrArg Prod.snd h
  norm_num at hlast

end PoincareConjecture
