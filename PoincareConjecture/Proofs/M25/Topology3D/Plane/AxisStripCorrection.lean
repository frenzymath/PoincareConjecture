import PoincareConjecture.Proofs.M25.Topology3D.Plane.AxisDerivative
import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedAxisJet
import PoincareConjecture.Proofs.M25.Topology3D.Plane.ThinStripExtension










set_option autoImplicit false

open Set
open scoped ContDiff Manifold

namespace PoincareConjecture.M25.Topology3D




theorem exists_axis_strip_correction
    (F : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ z x, x ∉ K → F z x = x)
    (haxis : ∀ z u : ℝ, (F z (u, 0)).2 = 0) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x : ℝ × ℝ, |x.2| < ε → F z x = x) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => C p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (C p.1).symm p.2) ∧
      (∀ z x, |x.2| ≤ δ → C z (F z x) = x) ∧
      (∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x, C z x = x) ∧
      ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → C z x = x ∧ (C z).symm x = x := by
  have hFi := contDiff_diffeomorph_family_symm F hF
  have hends (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (u : ℝ) : F z (u, 0) = (u, 0) :=
    hstrip z hz (u, 0) (by simpa only [abs_zero] using hε)
  obtain ⟨A, hA, hAi, hAaxis, hArel, _, _, ⟨QA, hQA, hAfix⟩, _⟩ :=
    exists_axis_pointwise_correction F hF hFi hK hfix haxis hends
  have hAend (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) : A z x = x :=
    hArel z (hends z hz) x
  let L : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun z => (F z).trans (A z)
  have hL : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => L p.1 p.2) :=
    hA.comp (contDiff_fst.prodMk hF)
  have hLaxis (z u : ℝ) : L z (u, 0) = (u, 0) := hAaxis z u
  let K₁ := K ∪ QA
  have hK₁ : IsCompact K₁ := hK.union hQA
  have hLfix (z : ℝ) (x : ℝ × ℝ) (hx : x ∉ K₁) : L z x = x := by
    change A z (F z x) = x
    rw [hfix z x (fun h => hx (Or.inl h)), (hAfix z x (fun h => hx (Or.inr h))).1]
  have hLstrip (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) (hx : |x.2| < ε) :
      L z x = x := by
    change A z (F z x) = x
    rw [hstrip z hz x hx, hAend z hz]
  obtain ⟨a, c, _, m, M, _, hm, ha, hc, hLjet, hbound, hacend, _, haK, hcK⟩ :=
    exists_fixed_axis_derivative_coefficients L hL hK₁ hLfix hLaxis hε hLstrip
  obtain ⟨D, hD, hDi, hDaxis, hDjet, hDrel, QD, hQD, hDfix⟩ :=
    exists_supported_axis_jet a c ha hc haK hcK hm hbound
  have hDend (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) : D z x = x :=
    hDrel z (fun u => hacend z u hz) x
  have hDiend (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) : (D z).symm x = x := by
    apply (D z).toEquiv.injective
    change D z ((D z).symm x) = D z x
    rw [Diffeomorph.apply_symm_apply, hDend z hz]
  let J : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun z => (L z).trans (D z).symm
  have hJ : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => J p.1 p.2) :=
    hDi.comp (contDiff_fst.prodMk hL)
  have hJaxis (z u : ℝ) : J z (u, 0) = (u, 0) := by
    change (D z).symm (L z (u, 0)) = (u, 0)
    rw [hLaxis, ← hDaxis z u, Diffeomorph.symm_apply_apply, hDaxis]
  have hJjet (z u : ℝ) : fderiv ℝ (J z) (u, 0) =
      ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
    have heq : fderiv ℝ (L z) (u, 0) = fderiv ℝ (D z) (u, 0) := by
      apply ContinuousLinearMap.ext
      intro w
      exact (hLjet z u w).trans (hDjet z u w).symm
    have hd := ((D z).contDiff.differentiable (by simp) (u, 0)).hasFDerivAt
    have hdi := ((D z).symm.contDiff.differentiable (by simp) (u, 0)).hasFDerivAt
    have hdiD := ((D z).symm.contDiff.differentiable (by simp) (D z (u, 0))).hasFDerivAt
    have hleft := hdiD.comp (u, 0) hd
    rw [hDaxis] at hleft
    have hid : ((D z).symm : (ℝ × ℝ) → ℝ × ℝ) ∘ (D z) = id :=
      funext (fun x => (D z).symm_apply_apply x)
    rw [hid] at hleft
    have hcancel := hleft.unique (hasFDerivAt_id (u, 0))
    have hl := ((L z).contDiff.differentiable (by simp) (u, 0)).hasFDerivAt
    have hdi' : HasFDerivAt ((D z).symm : (ℝ × ℝ) → ℝ × ℝ)
        (fderiv ℝ (D z).symm (u, 0)) (L z (u, 0)) := by
      rw [hLaxis]
      exact hdi
    have hh := hdi'.comp (u, 0) hl
    change HasFDerivAt (J z)
      ((fderiv ℝ (D z).symm (u, 0)).comp (fderiv ℝ (L z) (u, 0))) (u, 0) at hh
    rw [heq, hcancel] at hh
    exact hh.fderiv
  let K₂ := K₁ ∪ QD
  have hK₂ : IsCompact K₂ := hK₁.union hQD
  have hJfix (z : ℝ) (x : ℝ × ℝ) (hx : x ∉ K₂) : J z x = x := by
    change (D z).symm (L z x) = x
    rw [hLfix z x (fun h => hx (Or.inl h)), (hDfix z x (fun h => hx (Or.inr h))).2]
  have hJstrip (z : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) (x : ℝ × ℝ) (hx : |x.2| < ε) :
      J z x = x := by
    change (D z).symm (L z x) = x
    rw [hLstrip z hz x hx, hDiend z hz]
  obtain ⟨δ, hδ, E, hE, hEi, hEnear, hEend, hEfix⟩ :=
    exists_supported_strip_extension (fun p => J p.1 p.2) hJ hK₂ hJfix hJaxis hJjet hε
      hJstrip
  let C : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) :=
    fun z => ((A z).trans (D z).symm).trans (E z).symm
  have hC : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => C p.1 p.2) :=
    hEi.comp (contDiff_fst.prodMk (hDi.comp (contDiff_fst.prodMk hA)))
  have hCi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (C p.1).symm p.2) :=
    hAi.comp (contDiff_fst.prodMk (hD.comp (contDiff_fst.prodMk hE)))
  refine ⟨δ, hδ, C, hC, hCi, ?_, ?_, K₂, hK₂, ?_⟩
  · intro z x hx
    change (E z).symm (J z x) = x
    rw [← hEnear z x hx, Diffeomorph.symm_apply_apply]
  · intro z hz x
    change (E z).symm ((D z).symm (A z x)) = x
    rw [hAend z hz, hDiend z hz]
    apply (E z).toEquiv.injective
    change E z ((E z).symm x) = E z x
    rw [Diffeomorph.apply_symm_apply, hEend z hz]
  · intro z x hx
    have hAx : A z x = x := (hAfix z x (fun h => hx (Or.inl (Or.inr h)))).1
    have hDx : (D z).symm x = x := (hDfix z x (fun h => hx (Or.inr h))).2
    have hEx : (E z).symm x = x := (hEfix z x hx).2
    have hh : C z x = x := by
      change (E z).symm ((D z).symm (A z x)) = x
      rw [hAx, hDx, hEx]
    refine ⟨hh, ?_⟩
    have hi := congrArg (C z).symm hh
    simpa only [Diffeomorph.symm_apply_apply] using hi.symm

end PoincareConjecture.M25.Topology3D
