import PoincareConjecture.Proofs.Horizon.Topology.Manifold.Schoenflies.Morse.Models.Saddle.Global.Wall.Smoothing.Exterior.Caps.Replacement.Height



noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Metric Function Filter
open scoped Manifold ContDiff Topology

namespace Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Replacement



theorem exists_relative_cylindrical_height_correction
    (H : Real ≃ₘ[Real] Real) {σ b : Real} (hσ : 0 < σ) (hb : 0 < b)
    (hH : ∀ t, |t| ≤ σ → H t = t / Real.sqrt (1-t^2)) :
    ∃ ε : Real, 0 < ε ∧ ε < b ∧ ε ≤ σ ∧
      ∃ K : Real ≃ₘ[Real] Real, StrictMono K ∧
      (∀ t, |t| ≤ ε → K t = t) ∧
      (∀ t, b ≤ |t| → K t = H.symm t) := by
  obtain ⟨τ,hτ,hτb,hτsmall,D,hDmono,hDzero,hDlocal,hDoutside⟩ :=
    exists_cylindrical_height_diffeomorph hb
  let ε := min σ τ
  have hε : 0 < ε := lt_min hσ hτ
  let K := D.trans H.symm
  have hfix (t : Real) (ht : |t| ≤ ε) : K t = t := by
    change H.symm (D t) = t
    have hDt : D t = H t := (hDlocal t (ht.trans (min_le_right σ τ))).trans
      (hH t (ht.trans (min_le_left σ τ))).symm
    rw [hDt,H.symm_apply_apply]
  have hmono : StrictMono K := by
    rcases K.continuous.strictMono_of_inj K.injective with hm | hm
    · exact hm
    · have hh := hm hε
      rw [hfix 0 (by simpa using hε.le),hfix ε (by rw [abs_of_pos hε])] at hh
      linarith
  refine ⟨ε,hε,(min_le_right σ τ).trans_lt hτb,min_le_left σ τ,K,hmono,hfix,?_⟩
  intro t ht
  change H.symm (D t) = H.symm t
  rw [hDoutside t ht]

private theorem contDiff_upper_graft
    (f : Real → Real) (hf : ContDiff Real ∞ f) {ε : Real} (hε : 0 < ε)
    (hfix : ∀ t, |t| ≤ ε → f t = t) :
    ContDiff Real ∞ (fun t => if t ≤ 0 then t else f t) := by
  rw [contDiff_iff_contDiffAt]
  intro t
  rcases lt_trichotomy t 0 with ht | ht | ht
  · have heq : (fun s => if s ≤ 0 then s else f s) =ᶠ[𝓝 t] id := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      simp [(show s < 0 from hs).le]
    exact contDiffAt_id.congr_of_eventuallyEq heq
  · subst t
    have heq : (fun s => if s ≤ 0 then s else f s) =ᶠ[𝓝 (0 : Real)] id := by
      filter_upwards [Metric.ball_mem_nhds (0 : Real) hε] with s hs
      have hs' : |s| ≤ ε := (show |s| < ε by
        simpa only [mem_ball,Real.dist_eq,sub_zero] using hs).le
      simp [hfix s hs']
    exact contDiffAt_id.congr_of_eventuallyEq heq
  · have heq : (fun s => if s ≤ 0 then s else f s) =ᶠ[𝓝 t] f := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      simp [not_le.mpr (show 0 < s from hs)]
    exact hf.contDiffAt.congr_of_eventuallyEq heq



theorem exists_lower_fixed_cylindrical_height_correction
    (H : Real ≃ₘ[Real] Real) {σ b : Real} (hσ : 0 < σ) (hb : 0 < b)
    (hH : ∀ t, |t| ≤ σ → H t = t / Real.sqrt (1-t^2)) :
    ∃ ε : Real, 0 < ε ∧ ε < b ∧ ε ≤ σ ∧
      ∃ K : Real ≃ₘ[Real] Real, StrictMono K ∧
      (∀ t, t ≤ ε → K t = t) ∧
      (∀ t, b ≤ t → K t = H.symm t) := by
  obtain ⟨ε,hε,hεb,hεσ,L,hLmono,hLfix,hLoutside⟩ :=
    exists_relative_cylindrical_height_correction H hσ hb hH
  have hLzero : L 0 = 0 := hLfix 0 (by simpa using hε.le)
  have hLinvfix (t : Real) (ht : |t| ≤ ε) : L.symm t = t := by
    have hh := L.symm_apply_apply t
    rwa [hLfix t ht] at hh
  have hLpos {t : Real} (ht : 0 < t) : 0 < L t := by
    simpa only [hLzero] using hLmono ht
  have hLinvpos {t : Real} (ht : 0 < t) : 0 < L.symm t := by
    apply hLmono.lt_iff_lt.mp
    simpa only [hLzero,L.apply_symm_apply] using ht
  let K : Real ≃ₘ[Real] Real := {
    toFun t := if t ≤ 0 then t else L t
    invFun t := if t ≤ 0 then t else L.symm t
    left_inv t := by
      by_cases ht : t ≤ 0
      · simp only [if_pos ht]
      · simp only [if_neg ht,if_neg (not_le.mpr (hLpos (lt_of_not_ge ht))),
          L.symm_apply_apply]
    right_inv t := by
      by_cases ht : t ≤ 0
      · simp only [if_pos ht]
      · simp only [if_neg ht,if_neg (not_le.mpr (hLinvpos (lt_of_not_ge ht))),
          L.apply_symm_apply]
    contMDiff_toFun := (contDiff_upper_graft L L.contDiff hε hLfix).contMDiff
    contMDiff_invFun := (contDiff_upper_graft L.symm L.symm.contDiff hε hLinvfix).contMDiff }
  have hfix (t : Real) (ht : t ≤ ε) : K t = t := by
    change (if t ≤ 0 then t else L t) = t
    split_ifs with ht0
    · rfl
    · exact hLfix t (by rw [abs_of_pos (lt_of_not_ge ht0)]; exact ht)
  have hmono : StrictMono K := by
    rcases K.continuous.strictMono_of_inj K.injective with hm | hm
    · exact hm
    · have hh := hm hε
      rw [hfix 0 hε.le,hfix ε le_rfl] at hh
      linarith
  refine ⟨ε,hε,hεb,hεσ,K,hmono,hfix,?_⟩
  intro t ht
  have htpos : 0 < t := hb.trans_le ht
  change (if t ≤ 0 then t else L t) = H.symm t
  rw [if_neg (not_le.mpr htpos)]
  exact hLoutside t (by rwa [abs_of_pos htpos])

end Poincare.Manifold.Schoenflies.Saddle.Wall.Smoothing.Exterior.Caps.Replacement
