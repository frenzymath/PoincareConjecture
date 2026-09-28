import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Algebra.Support










set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_translation_conjugate_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : E ≃ₘ[ℝ] E) (v : E) (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ)
    (hθrange : ∀ z, θ z ∈ Icc 0 1) {K : Set E} (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → h x = x) :
    ∃ F : ℝ → (E ≃ₘ[ℝ] E),
      ContDiff ℝ ∞ (fun p : ℝ × E => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × E => (F p.1).symm p.2) ∧
      (∀ z x, F z x = h (x + θ z • v) - θ z • v) ∧
      (∀ z x, (F z).symm x = h.symm (x + θ z • v) - θ z • v) ∧
      (∃ Q : Set E, IsCompact Q ∧
        ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
      ∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x) := by
  let f : ℝ → E → E := fun z x => h (x + θ z • v) - θ z • v
  let g : ℝ → E → E := fun z x => h.symm (x + θ z • v) - θ z • v
  have hv : ContDiff ℝ ∞ (fun p : ℝ × E => θ p.1 • v) :=
    (hθ.comp contDiff_fst).smul contDiff_const
  have hf : ContDiff ℝ ∞ (fun p : ℝ × E => f p.1 p.2) :=
    (h.contDiff.comp (contDiff_snd.add hv)).sub hv
  have hg : ContDiff ℝ ∞ (fun p : ℝ × E => g p.1 p.2) :=
    (h.symm.contDiff.comp (contDiff_snd.add hv)).sub hv
  let F : ℝ → (E ≃ₘ[ℝ] E) := fun z =>
    { toEquiv :=
        { toFun := f z
          invFun := g z
          left_inv := fun x => by
            simp only [f, g, sub_add_cancel, Diffeomorph.symm_apply_apply, add_sub_cancel_right]
          right_inv := fun x => by
            simp only [f, g, sub_add_cancel, Diffeomorph.apply_symm_apply, add_sub_cancel_right] }
      contMDiff_toFun := (hf.comp (contDiff_const.prodMk contDiff_id)).contMDiff
      contMDiff_invFun := (hg.comp (contDiff_const.prodMk contDiff_id)).contMDiff }
  let Q : Set E := (fun p : ℝ × E => p.2 - p.1 • v) '' (Icc 0 1 ×ˢ K)
  have hQ : IsCompact Q := (isCompact_Icc.prod hK).image
    (continuous_snd.sub (continuous_fst.smul continuous_const))
  have hfixed (z : ℝ) (x : E) (hx : x ∉ Q) : F z x = x ∧ (F z).symm x = x := by
    have hshift : x + θ z • v ∉ K := by
      intro hm
      exact hx ⟨(θ z, x + θ z • v), ⟨hθrange z, hm⟩, add_sub_cancel_right x _⟩
    have hh := hfix (x + θ z • v) hshift
    have hhi : h.symm (x + θ z • v) = x + θ z • v := by
      have he := congrArg h.symm hh
      simpa only [Diffeomorph.symm_apply_apply] using he.symm
    change h (x + θ z • v) - θ z • v = x ∧ h.symm (x + θ z • v) - θ z • v = x
    rw [hh, hhi, add_sub_cancel_right]
    exact ⟨rfl, rfl⟩
  refine ⟨F, hf, hg, (fun _ _ => rfl), (fun _ _ => rfl), ⟨Q, hQ, hfixed⟩, ?_⟩
  intro z
  exact ⟨HasCompactSupport.intro hQ (fun x hx => sub_eq_zero.mpr (hfixed z x hx).1),
    HasCompactSupport.intro hQ (fun x hx => sub_eq_zero.mpr (hfixed z x hx).2)⟩




theorem exists_munkres_slide (h : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → h x = x)
    {b d : ℝ} (hb : 0 < b) (hd : 0 < d)
    (hlower : ∀ x : ℝ × ℝ, x.2 < d → h x = x)
    (hupper : ∀ x : ℝ × ℝ, b / 2 ≤ x.2 → h x = x) :
    ∃ F : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (F p.1).symm p.2) ∧
      (∀ z x, F z x = h (x + Real.smoothTransition (3 * z - 1) • (0, b)) -
        Real.smoothTransition (3 * z - 1) • (0, b)) ∧
      (∀ z, z ≤ 1 / 3 → ∀ x, F z x = h x) ∧
      (∀ z, 2 / 3 ≤ z → ∀ x : ℝ × ℝ, 0 ≤ x.2 → F z x = x) ∧
      (∃ ε : ℝ, 0 < ε ∧ ∀ z, z ≤ 1 / 3 ∨ 2 / 3 ≤ z →
        ∀ x : ℝ × ℝ, |x.2| < ε → F z x = x) ∧
      ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 (p.2, 0)) ∧
      (∀ z, Injective (fun u : ℝ => F z (u, 0))) ∧
      (∀ z u : ℝ, deriv (fun s => F z (s, 0)) u ≠ 0) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → F z x = x ∧ (F z).symm x = x) ∧
      ∀ z, HasCompactSupport (fun x => F z x - x) ∧
        HasCompactSupport (fun x => (F z).symm x - x) := by
  let α : ℝ → ℝ := fun z => Real.smoothTransition (3 * z - 1)
  have hα : ContDiff ℝ ∞ α := Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)
  have hαrange (z : ℝ) : α z ∈ Icc 0 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hα0 (z : ℝ) (hz : z ≤ 1 / 3) : α z = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hα1 (z : ℝ) (hz : 2 / 3 ≤ z) : α z = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  obtain ⟨F, hF, hFi, hformula, _, hQ, hcompact⟩ :=
    exists_translation_conjugate_family h (0, b) α hα hαrange hK hfix
  have hstart (z : ℝ) (hz : z ≤ 1 / 3) (x : ℝ × ℝ) : F z x = h x := by
    rw [hformula, hα0 z hz, zero_smul, add_zero, sub_zero]
  have hend (z : ℝ) (hz : 2 / 3 ≤ z) (x : ℝ × ℝ) (hx : b / 2 ≤ x.2 + b) :
      F z x = x := by
    rw [hformula, hα1 z hz, one_smul, hupper (x + (0, b)) hx, add_sub_cancel_right]
  have hcurve : ContDiff ℝ ∞ (fun p : ℝ × ℝ => F p.1 (p.2, 0)) :=
    hF.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))
  refine ⟨F, hF, hFi, hformula, hstart, ?_, ?_, hcurve, ?_, ?_, hQ, hcompact⟩
  · intro z hz x hx
    exact hend z hz x (by linarith)
  · refine ⟨min d (b / 4), lt_min hd (by linarith), ?_⟩
    intro z hz x hx
    rcases hz with hz | hz
    · rw [hstart z hz]
      exact hlower x (lt_of_lt_of_le (lt_of_le_of_lt (le_abs_self _) hx) (min_le_left _ _))
    · apply hend z hz x
      have hy := (abs_lt.mp hx).1
      have he := min_le_right d (b / 4)
      linarith
  · intro z u v huv
    exact congrArg Prod.fst ((F z).toEquiv.injective huv)
  · intro z u hzero
    have hs : ContDiff ℝ ∞ (fun s : ℝ => F z (s, 0)) :=
      (F z).contDiff.comp (contDiff_id.prodMk contDiff_const)
    have houter := ((F z).symm.contDiff.differentiable (by simp) (F z (u, 0))).hasFDerivAt
    have hh := houter.comp_hasDerivAt u ((hs.differentiable (by simp) u).hasDerivAt)
    have heq : ((F z).symm : (ℝ × ℝ) → (ℝ × ℝ)) ∘ (fun s : ℝ => F z (s, 0)) =
        (fun s : ℝ => (s, 0)) := by
      funext s
      exact (F z).symm_apply_apply _
    rw [heq, hzero, map_zero] at hh
    have hbad : (1, (0 : ℝ)) = (0 : ℝ × ℝ) :=
      ((hasDerivAt_id u).prodMk (hasDerivAt_const u (0 : ℝ))).deriv.symm.trans hh.deriv
    have hbadfst := congrArg Prod.fst hbad
    norm_num at hbadfst

end PoincareConjecture.M25.Topology3D
