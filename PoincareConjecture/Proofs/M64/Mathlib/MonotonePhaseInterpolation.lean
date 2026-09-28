import PoincareConjecture.Proofs.M64.Mathlib.MonotoneIntervalReplacement
import PoincareConjecture.Proofs.M64.Mathlib.MonotoneAffineExtension

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open Set

namespace PoincareConjecture

theorem m64Monotone_phase_chord_replacement
    {P D a b : ℝ} (hP : 0 < P) (ha : 0 < a) (hab : a < b) (hb : b < P)
    (H : ℝ ≃o ℝ) (hH : ∀ x, H (x + P) = H x + D)
    (sigma : ℝ → ℝ) (hc : Continuous sigma) (hm : Monotone sigma)
    (hp : ∀ x, sigma (x + P) = sigma x + P) :
    ∃ tau : ℝ → ℝ, Continuous tau ∧ Monotone tau ∧
      (∀ x, tau (x + P) = tau x + P) ∧ tau 0 = sigma 0 ∧
      (∀ x ∈ Icc a b, H (tau x) =
        AffineMap.lineMap (H (sigma a)) (H (sigma b)) ((x - a) / (b - a))) ∧
      EqOn tau sigma (Icc 0 P \ Icc a b) := by
  classical
  let f := H ∘ sigma
  let g := fun x => AffineMap.lineMap (f a) (f b) ((x - a) / (b - a))
  have hfc : Continuous f := H.continuous.comp hc
  have hfm : Monotone f := H.monotone.comp hm
  have hgc : Continuous g := by
    dsimp only [g, AffineMap.lineMap_apply_module]
    fun_prop
  have hgm : Monotone g := (AffineMap.lineMap_mono (hfm hab.le)).comp
    (fun _ _ hxy => div_le_div_of_nonneg_right (sub_le_sub_right hxy a) (sub_pos.mpr hab).le)
  have hga : g a = f a := by simp [g]
  have hgb : g b = f b := by simp [g, (sub_pos.mpr hab).ne']
  let v := (Icc a b).piecewise g f
  obtain ⟨hvc, hvm⟩ := m64Monotone_interval_replacement hab.le hfc hgc hfm hgm hga hgb
  have h0 : v 0 = f 0 := piecewise_eq_of_notMem _ _ _ (by
    intro h
    exact (not_le_of_gt ha) h.1)
  have hPval : v P = f P := piecewise_eq_of_notMem _ _ _ (by
    intro h
    exact (not_le_of_gt hb) h.2)
  have hvends : v P = v 0 + D := by
    rw [h0, hPval]
    dsimp only [f, Function.comp_def]
    have hs := hp 0
    simp only [zero_add] at hs
    rw [hs, hH]
  obtain ⟨F, hFc, hFm, hFp, hFeq⟩ := m64Monotone_affine_periodic_extension hP v
    hvc.continuousOn (hvm.monotoneOn _) hvends
  let tau := H.symm ∘ F
  have hHt (x : ℝ) : H (tau x) = F x := H.apply_symm_apply _
  have htp (x : ℝ) : tau (x + P) = tau x + P := by
    apply H.injective
    rw [hHt, hH, hHt, hFp]
  have ht0 : tau 0 = sigma 0 := by
    apply H.injective
    rw [hHt, hFeq ⟨le_rfl, hP.le⟩, h0]
    rfl
  refine ⟨tau, H.symm.continuous.comp hFc, H.symm.monotone.comp hFm, htp, ht0, ?_, ?_⟩
  · intro x hx
    rw [hHt, hFeq ⟨ha.le.trans hx.1, hx.2.trans hb.le⟩]
    exact piecewise_eq_of_mem _ _ _ hx
  · intro x hx
    apply H.injective
    rw [hHt, hFeq hx.1]
    exact piecewise_eq_of_notMem _ _ _ hx.2

end PoincareConjecture
