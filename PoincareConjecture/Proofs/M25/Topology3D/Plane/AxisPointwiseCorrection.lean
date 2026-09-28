import PoincareConjecture.Proofs.M25.Topology3D.Plane.VerticalInterpolation
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TimePreservingFibers
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D

theorem exists_axis_pointwise_correction
    (F : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2))
    (hFi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (F p.1).symm p.2))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ z x, x ∉ K → F z x = x)
    (haxis : ∀ z u : ℝ, (F z (u, 0)).2 = 0)
    (hends : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ u : ℝ, F z (u, 0) = (u, 0)) :
    ∃ C : ℝ → ((ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ)),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => C p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (C p.1).symm p.2) ∧
      (∀ z u : ℝ, C z (F z (u, 0)) = (u, 0)) ∧
      (∀ z, (∀ u : ℝ, F z (u, 0) = (u, 0)) → ∀ x, C z x = x) ∧
      (∀ z x, (C z x).2 = x.2) ∧
      (∀ z x, (C z x).1 =
        lineInterpolation (fun u => ((F z).symm (u, 0)).1)
          (Real.smoothTransition (2 - x.2 ^ 2)) x.1) ∧
      (∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → C z x = x ∧ (C z).symm x = x) ∧
      ∀ z, HasCompactSupport (fun x => C z x - x) ∧
        HasCompactSupport (fun x => (C z).symm x - x) := by
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let φ : ℝ → ℝ → ℝ := fun z u => (F z (u, 0)).1
  let ψ : ℝ → ℝ → ℝ := fun z u => ((F z).symm (u, 0)).1
  have hφ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => φ p.1 p.2) :=
    (hF.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).fst
  have hψ : ContDiff ℝ ∞ (fun p : ℝ × ℝ => ψ p.1 p.2) :=
    (hFi.comp (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))).fst
  have hFaxis (z u : ℝ) : F z (u, 0) = (φ z u, 0) := Prod.ext rfl (haxis z u)
  have htail (z u : ℝ) (hu : u ≤ -R ∨ R ≤ u) :
      φ z u = u ∧ ψ z u = u := by
    have hout : (u, (0 : ℝ)) ∉ K := by
      intro hm
      have hh : |u| < R := by simpa using hbound (u, 0) hm
      rcases hu with hu | hu
      · linarith [(abs_lt.mp hh).1]
      · linarith [(abs_lt.mp hh).2]
    have hh := hfix z (u, 0) hout
    have hhi := congrArg (F z).symm hh
    exact ⟨congrArg Prod.fst hh, congrArg Prod.fst (by
      simpa only [Diffeomorph.symm_apply_apply] using hhi.symm)⟩
  have hleft (z : ℝ) : LeftInverse (ψ z) (φ z) := by
    intro u
    have hh := congrArg Prod.fst ((F z).symm_apply_apply (u, 0))
    rw [hFaxis] at hh
    exact hh
  have hsurj (z : ℝ) : Surjective (φ z) :=
    surjective_of_eq_self_outside_interval
      (hφ.continuous.comp (continuous_const.prodMk continuous_id)) (-R) R
      (fun u hu => (htail z u hu).1)
  have hright (z : ℝ) : LeftInverse (φ z) (ψ z) := by
    intro v
    obtain ⟨u, rfl⟩ := hsurj z v
    rw [hleft z u]
  have hpositive (z u : ℝ) : 0 < deriv (ψ z) u := by
    have hψz : ContDiff ℝ ∞ (ψ z) := hψ.comp (contDiff_const.prodMk contDiff_id)
    have hφz : ContDiff ℝ ∞ (φ z) := hφ.comp (contDiff_const.prodMk contDiff_id)
    have hmono : StrictMono (ψ z) := by
      rcases hψz.continuous.strictMono_of_inj (hright z).injective with hm | ha
      · exact hm
      · have hh := ha (show R < R + 1 by linarith)
        rw [(htail z R (Or.inr le_rfl)).2,
          (htail z (R + 1) (Or.inr (by linarith))).2] at hh
        linarith
    have hne : deriv (ψ z) u ≠ 0 := by
      intro hz
      have hdφ := (hφz.differentiable (by simp) (ψ z u)).hasDerivAt
      have hdψ := (hψz.differentiable (by simp) u).hasDerivAt
      have hh := hdφ.comp u hdψ
      have heq : φ z ∘ ψ z = id := funext (hright z)
      rw [heq, hz, mul_zero] at hh
      have hbad := hh.deriv
      norm_num at hbad
    exact lt_of_le_of_ne hmono.monotone.deriv_nonneg (Ne.symm hne)
  let ρ : ℝ → ℝ := fun y => Real.smoothTransition (2 - y ^ 2)
  have hρ : ContDiff ℝ ∞ ρ :=
    Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_id.pow 2))
  have hρrange (y : ℝ) : ρ y ∈ Icc 0 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  have hρzero (y : ℝ) (hy : y ≤ -2 ∨ 2 ≤ y) : ρ y = 0 := by
    apply Real.smoothTransition.zero_of_nonpos
    rcases hy with hy | hy <;> nlinarith [sq_nonneg (y + 2), sq_nonneg (y - 2)]
  have hρ0 : ρ 0 = 1 := by norm_num [ρ, Real.smoothTransition.one_of_one_le]
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p => ψ p.1.1 p.2
  let τ : ℝ × ℝ → ℝ := fun p => ρ p.2
  have hf : ContDiff ℝ ∞ f :=
    hψ.comp ((contDiff_fst.comp contDiff_fst).prodMk contDiff_snd)
  have hτ : ContDiff ℝ ∞ τ := hρ.comp contDiff_snd
  have hfpos (p : ℝ × ℝ) (u : ℝ) : 0 < deriv (fun v => f (p, v)) u :=
    hpositive p.1 u
  have hftail (p : ℝ × ℝ) (u : ℝ) (hu : u ≤ -R ∨ R ≤ u) : f (p, u) = u :=
    (htail p.1 u hu).2
  let J := verticalInterpolationDiffeomorph hf hτ (fun p => hρrange p.2) hfpos
    (-R) R hftail
  let B : (ℝ × (ℝ × ℝ)) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
        (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm
  let D := (B.toDiffeomorph.trans J).trans B.toDiffeomorph.symm
  have hD (p : ℝ × (ℝ × ℝ)) :
      D p = (p.1, (lineInterpolation (ψ p.1) (ρ p.2.2) p.2.1, p.2.2)) := rfl
  have hinvfix (z : ℝ) (hz : ∀ u : ℝ, F z (u, 0) = (u, 0)) (u : ℝ) : ψ z u = u := by
    have hh := congrArg (F z).symm (hz u)
    have he : (F z).symm (u, 0) = (u, 0) := by
      simpa only [Diffeomorph.symm_apply_apply] using hh.symm
    exact congrArg Prod.fst he
  have hcompact : HasCompactSupport (fun p => D p - p) := by
    apply HasCompactSupport.intro
      (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc) :
        IsCompact (Icc (0 : ℝ) 1 ×ˢ (Icc (-R) R ×ˢ Icc (-2 : ℝ) 2)))
    intro p hp
    apply sub_eq_zero.mpr
    rw [hD]
    suffices hh : lineInterpolation (ψ p.1) (ρ p.2.2) p.2.1 = p.2.1 by
      rw [hh]
    by_cases hz : p.1 ∈ Icc (0 : ℝ) 1
    · by_cases hu : p.2.1 ∈ Icc (-R) R
      · have hy : p.2.2 ≤ -2 ∨ 2 ≤ p.2.2 := by
          by_contra hn
          push Not at hn
          exact hp ⟨hz, hu, hn.1.le, hn.2.le⟩
        rw [hρzero _ hy, lineInterpolation_zero]
      · apply lineInterpolation_eq_self
        apply (htail p.1 p.2.1 _).2
        by_contra hn
        push Not at hn
        exact hu ⟨hn.1.le, hn.2.le⟩
    · apply lineInterpolation_eq_self
      apply hinvfix _ (hends _ _)
      by_contra hn
      push Not at hn
      exact hz ⟨hn.1.le, hn.2.le⟩
  obtain ⟨C, hC, _, hCs, hCi, hQ, hsupport⟩ :=
    exists_time_preserving_diffeomorph_fibers D (fun p => by rw [hD]) hcompact
  have hformula (z : ℝ) (x : ℝ × ℝ) :
      C z x = (lineInterpolation (ψ z) (ρ x.2) x.1, x.2) := by
    rw [hC, hD]
  refine ⟨C, hCs, hCi, ?_, ?_, ?_, ?_, hQ, hsupport⟩
  · intro z u
    rw [hFaxis, hformula, hρ0, lineInterpolation_one, hleft z u]
  · intro z hz x
    rw [hformula, lineInterpolation_eq_self (hinvfix z hz x.1)]
  · intro z x
    rw [hformula]
  · intro z x
    exact congrArg Prod.fst (hformula z x)

end PoincareConjecture.M25.Topology3D
