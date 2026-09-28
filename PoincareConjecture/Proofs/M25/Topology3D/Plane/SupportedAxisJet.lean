import PoincareConjecture.Proofs.M25.Topology3D.Plane.SupportedLinearProfile
import PoincareConjecture.Proofs.M25.Topology3D.Plane.TimePreservingFibers
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Module.Equiv

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

theorem exists_supported_normal_scaling_family (c : ℝ × ℝ → ℝ)
    (hc : ContDiff ℝ ∞ c) (hcompact : HasCompactSupport (fun p => c p - 1))
    {m M : ℝ} (hm : 0 < m) (hbound : ∀ p, m ≤ c p ∧ c p ≤ M) :
    ∃ V : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => V p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (V p.1).symm p.2) ∧
      (∀ z x, (V z x).1 = x.1) ∧
      (∀ z x, |x.2| ≤ 1 → V z x = (x.1, c (z, x.1) * x.2)) ∧
      (∀ z x, c (z, x.1) = 1 → V z x = x) ∧
      ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → V z x = x ∧ (V z).symm x = x := by
  obtain ⟨R, _, J, _, hnear, htail, hunit, η, _, hformula⟩ :=
    exists_supported_positive_scaling c hc hm hbound
  let B := (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm
  let D := (B.toDiffeomorph.trans J).trans B.toDiffeomorph.symm
  have hD (p : ℝ × (ℝ × ℝ)) :
      D p = (p.1, (p.2.1, p.2.2 + (c (p.1, p.2.1) - 1) * η p.2.2)) := by
    change B.symm (J ((p.1, p.2.1), p.2.2)) = _
    rw [hformula]
    rfl
  have hDnear (p : ℝ × (ℝ × ℝ)) (hp : |p.2.2| ≤ 1) :
      D p = (p.1, (p.2.1, c (p.1, p.2.1) * p.2.2)) := by
    change B.symm (J ((p.1, p.2.1), p.2.2)) = _
    rw [hnear _ _ hp]
    rfl
  have hDtail (p : ℝ × (ℝ × ℝ)) (hp : R ≤ |p.2.2|) : D p = p := by
    change B.symm (J ((p.1, p.2.1), p.2.2)) = _
    rw [htail _ _ hp]
    rfl
  have hDunit (p : ℝ × (ℝ × ℝ)) (hp : c (p.1, p.2.1) = 1) : D p = p := by
    change B.symm (J ((p.1, p.2.1), p.2.2)) = _
    rw [hunit _ hp]
    rfl
  obtain ⟨K, hK, hKzero⟩ := exists_compact_iff_hasCompactSupport.mpr hcompact
  have hsupport : HasCompactSupport (fun p => D p - p) := by
    apply HasCompactSupport.intro
      ((hK.prod isCompact_Icc).image B.symm.continuous :
        IsCompact (B.symm '' (K ×ˢ Icc (-R) R)))
    intro p hp
    apply sub_eq_zero.mpr
    by_cases hk : (p.1, p.2.1) ∈ K
    · apply hDtail
      by_contra hy
      exact hp ⟨((p.1, p.2.1), p.2.2),
        ⟨hk, abs_le.mp (lt_of_not_ge hy).le⟩, rfl⟩
    · exact hDunit p (sub_eq_zero.mp (hKzero _ hk))
  obtain ⟨V, hV, _, hVs, hVi, hQ, _⟩ :=
    exists_time_preserving_diffeomorph_fibers D (fun p => by rw [hD]) hsupport
  refine ⟨V, hVs, hVi, ?_, ?_, ?_, hQ⟩
  · intro z x
    rw [hV, hD]
  · intro z x hx
    rw [hV, hDnear (z, x) hx]
  · intro z x hx
    rw [hV, hDunit (z, x) hx]

theorem exists_supported_axis_shear (a : ℝ × ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hcompact : HasCompactSupport a) :
    ∃ r : ℝ, 0 < r ∧ ∃ W : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => W p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (W p.1).symm p.2) ∧
      (∀ z x, (W z x).2 = x.2) ∧
      (∀ z x, |x.2| ≤ r → W z x = (x.1 + a (z, x.1) * x.2, x.2)) ∧
      (∀ z x, a (z, x.1) = 0 → W z x = x) ∧
      ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → W z x = x ∧ (W z).symm x = x := by
  let A : ℝ × ℝ → ℝ := fun p => fderiv ℝ a p (0, 1)
  have hA : ContDiff ℝ ∞ A :=
    (ha.fderiv_right (by simp) : ContDiff ℝ ∞ (fderiv ℝ a)).clm_apply contDiff_const
  obtain ⟨C, hC⟩ := (hcompact.fderiv_apply ℝ (0, 1)).exists_bound_of_continuous
    hA.continuous
  let B := max C 0 + 1
  have hB : 0 < B := by dsimp [B]; linarith [le_max_right C 0]
  have hAB (p : ℝ × ℝ) : |A p| ≤ B := by
    have hh := hC p
    rw [Real.norm_eq_abs] at hh
    exact hh.trans (by dsimp [B]; linarith [le_max_left C 0])
  let r := 1 / (4 * (B + 1))
  have hr : 0 < r := by dsimp [r]; positivity
  have hrval : r * (4 * (B + 1)) = 1 := one_div_mul_cancel (by positivity)
  have hsmall : B * (2 * r) < 1 := by nlinarith
  let ζ : ℝ → ℝ := fun y => y * Real.smoothTransition (2 - (y / r) ^ 2)
  have hζ : ContDiff ℝ ∞ ζ := contDiff_id.mul
    (Real.smoothTransition.contDiff.comp (contDiff_const.sub ((contDiff_id.div_const r).pow 2)))
  have hζnear (y : ℝ) (hy : |y| ≤ r) : ζ y = y := by
    have hq : |y / r| ≤ 1 := by
      rw [abs_div, abs_of_pos hr]
      exact (div_le_iff₀ hr).mpr (by simpa using hy)
    have hh := abs_le.mp hq
    have hone : Real.smoothTransition (2 - (y / r) ^ 2) = 1 :=
      Real.smoothTransition.one_of_one_le (by
        nlinarith [mul_nonneg (sub_nonneg.mpr hh.2) (by linarith : 0 ≤ y / r + 1)])
    simp only [ζ, hone, mul_one]
  have hζzero (y : ℝ) (hy : 2 * r ≤ |y|) : ζ y = 0 := by
    have hq : 2 ≤ |y / r| := by
      rw [abs_div, abs_of_pos hr]
      exact (le_div_iff₀ hr).mpr hy
    have hzero : Real.smoothTransition (2 - (y / r) ^ 2) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by
        nlinarith [sq_abs (y / r), mul_nonneg (sub_nonneg.mpr hq)
          (by positivity : 0 ≤ |y / r| + 2)])
    simp only [ζ, hzero, mul_zero]
  have hζbound (y : ℝ) : |ζ y| ≤ 2 * r := by
    by_cases hy : 2 * r ≤ |y|
    · rw [hζzero y hy, abs_zero]
      positivity
    · calc
        |ζ y| = |y| * Real.smoothTransition (2 - (y / r) ^ 2) := by
          dsimp only [ζ]
          rw [abs_mul, abs_of_nonneg (Real.smoothTransition.nonneg _)]
        _ ≤ |y| * 1 := mul_le_mul_of_nonneg_left
          (Real.smoothTransition.le_one _) (abs_nonneg _)
        _ ≤ 2 * r := by simpa using (lt_of_not_ge hy).le
  let f : (ℝ × ℝ) × ℝ → ℝ := fun p => p.2 + a (p.1.1, p.2) * ζ p.1.2
  have hf : ContDiff ℝ ∞ f := contDiff_snd.add
    ((ha.comp (contDiff_fst.fst.prodMk contDiff_snd)).mul (hζ.comp contDiff_fst.snd))
  have hd (p : ℝ × ℝ) (x : ℝ) : HasDerivAt (fun u => f (p, u))
      (1 + A (p.1, x) * ζ p.2) x := by
    have ha' : HasDerivAt (fun u => a (p.1, u)) (A (p.1, x)) x :=
      (ha.differentiable (by simp) (p.1, x)).hasFDerivAt.comp_hasDerivAt x
        ((hasDerivAt_const x p.1).prodMk (hasDerivAt_id x))
    exact (hasDerivAt_id x).add (ha'.mul_const (ζ p.2))
  have hpos (p : ℝ × ℝ) (x : ℝ) : 0 < deriv (fun u => f (p, u)) x := by
    rw [(hd p x).deriv]
    have hh : |A (p.1, x) * ζ p.2| < 1 := calc
      _ = |A (p.1, x)| * |ζ p.2| := abs_mul _ _
      _ ≤ B * (2 * r) := mul_le_mul (hAB _) (hζbound _) (abs_nonneg _) hB.le
      _ < 1 := hsmall
    linarith [(abs_lt.mp hh).1]
  obtain ⟨K, hK, hKzero⟩ := exists_compact_iff_hasCompactSupport.mpr hcompact
  obtain ⟨L, _, hLbound⟩ := hK.isBounded.exists_pos_norm_lt
  have htail (p : ℝ × ℝ) (x : ℝ) (hx : x ≤ -L ∨ L ≤ x) : f (p, x) = x := by
    have hxL : L ≤ |x| := by
      rcases hx with hx | hx
      · linarith [neg_le_abs x]
      · exact hx.trans (le_abs_self x)
    have hnot : (p.1, x) ∉ K := by
      intro hk
      have hh := (norm_snd_le (p.1, x)).trans_lt (hLbound _ hk)
      rw [Real.norm_eq_abs] at hh
      exact (not_lt_of_ge hxL) hh
    simp only [f, hKzero _ hnot, zero_mul, add_zero]
  have hsurj (p : ℝ × ℝ) : Surjective (fun x => f (p, x)) :=
    surjective_of_eq_self_outside_interval
      (hf.continuous.comp (continuous_const.prodMk continuous_id)) (-L) L (htail p)
  let J := fiberDiffeomorph hf hpos hsurj
  let U : (ℝ × (ℝ × ℝ)) ≃L[ℝ] ((ℝ × ℝ) × ℝ) :=
    ((ContinuousLinearEquiv.refl ℝ ℝ).prodCongr
      (ContinuousLinearEquiv.prodComm ℝ ℝ ℝ)).trans
        (ContinuousLinearEquiv.prodAssoc ℝ ℝ ℝ ℝ).symm
  let D := (U.toDiffeomorph.trans J).trans U.toDiffeomorph.symm
  have hD (p : ℝ × (ℝ × ℝ)) :
      D p = (p.1, (p.2.1 + a (p.1, p.2.1) * ζ p.2.2, p.2.2)) := rfl
  let O : (ℝ × ℝ) × ℝ → ℝ × (ℝ × ℝ) := fun p => (p.1.1, (p.1.2, p.2))
  have hO : Continuous O := continuous_fst.fst.prodMk
    (continuous_fst.snd.prodMk continuous_snd)
  have hsupport : HasCompactSupport (fun p => D p - p) := by
    apply HasCompactSupport.intro
      ((hK.prod isCompact_Icc).image hO : IsCompact (O '' (K ×ˢ Icc (-2 * r) (2 * r))))
    intro p hp
    apply sub_eq_zero.mpr
    rw [hD]
    by_cases hk : (p.1, p.2.1) ∈ K
    · have hy : 2 * r ≤ |p.2.2| := by
        by_contra hn
        have hh := abs_le.mp (lt_of_not_ge hn).le
        exact hp ⟨((p.1, p.2.1), p.2.2), ⟨hk, by simpa using hh⟩, rfl⟩
      simp only [hζzero _ hy, mul_zero, add_zero, Prod.mk.eta]
    · simp only [hKzero _ hk, zero_mul, add_zero, Prod.mk.eta]
  obtain ⟨W, hW, _, hWs, hWi, hQ, _⟩ :=
    exists_time_preserving_diffeomorph_fibers D (fun p => by rw [hD]) hsupport
  refine ⟨r, hr, W, hWs, hWi, ?_, ?_, ?_, hQ⟩
  · intro z x
    rw [hW, hD]
  · intro z x hx
    rw [hW, hD, hζnear _ hx]
  · intro z x hx
    simp only [hW, hD, hx, zero_mul, add_zero, Prod.mk.eta]

private theorem axis_product_hasFDerivAt (b : ℝ → ℝ) (hb : ContDiff ℝ ∞ b) (u : ℝ) :
    HasFDerivAt (fun x : ℝ × ℝ => b x.1 * x.2)
      (b u • ContinuousLinearMap.snd ℝ ℝ ℝ) (u, 0) := by
  have hdb : HasFDerivAt (fun x : ℝ × ℝ => b x.1)
      (fderiv ℝ (fun x : ℝ × ℝ => b x.1) (u, 0)) (u, 0) :=
    ((hb.comp contDiff_fst).differentiable (by simp) (u, (0 : ℝ))).hasFDerivAt
  simpa only [zero_smul, add_zero] using hdb.fun_mul (hasFDerivAt_snd :
    HasFDerivAt (Prod.snd : ℝ × ℝ → ℝ) (ContinuousLinearMap.snd ℝ ℝ ℝ) (u, 0))

theorem exists_supported_axis_jet (a c : ℝ × ℝ → ℝ)
    (ha : ContDiff ℝ ∞ a) (hc : ContDiff ℝ ∞ c) (haK : HasCompactSupport a)
    (hcK : HasCompactSupport (fun p => c p - 1)) {m M : ℝ} (hm : 0 < m)
    (hbound : ∀ p, m ≤ c p ∧ c p ≤ M) :
    ∃ D : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ),
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => D p.1 p.2) ∧
      ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (D p.1).symm p.2) ∧
      (∀ z u, D z (u, 0) = (u, 0)) ∧
      (∀ z u w, fderiv ℝ (D z) (u, 0) w =
        (w.1 + a (z, u) * w.2, c (z, u) * w.2)) ∧
      (∀ z, (∀ u, a (z, u) = 0 ∧ c (z, u) = 1) → ∀ x, D z x = x) ∧
      ∃ Q : Set (ℝ × ℝ), IsCompact Q ∧
        ∀ z x, x ∉ Q → D z x = x ∧ (D z).symm x = x := by
  obtain ⟨V, hVs, hVi, _, hVnear, hVunit, QV, hQV, hVfix⟩ :=
    exists_supported_normal_scaling_family c hc hcK hm hbound
  obtain ⟨r, hr, W, hWs, hWi, _, hWnear, hWzero, QW, hQW, hWfix⟩ :=
    exists_supported_axis_shear a ha haK
  have hWaxis (z u : ℝ) : W z (u, 0) = (u, 0) := by
    simpa using hWnear z (u, 0) (by simpa using hr.le)
  have hVaxis (z u : ℝ) : V z (u, 0) = (u, 0) := by
    simpa using hVnear z (u, 0) (by norm_num)
  let D : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ) := fun z => (W z).trans (V z)
  have hDs : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => D p.1 p.2) :=
    hVs.comp (contDiff_fst.prodMk hWs)
  have hDi : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => (D p.1).symm p.2) :=
    hWi.comp (contDiff_fst.prodMk hVi)
  refine ⟨D, hDs, hDi, ?_, ?_, ?_, QV ∪ QW, hQV.union hQW, ?_⟩
  · intro z u
    change V z (W z (u, 0)) = _
    rw [hWaxis, hVaxis]
  · intro z u w
    let AW := (ContinuousLinearMap.fst ℝ ℝ ℝ + a (z, u) •
      ContinuousLinearMap.snd ℝ ℝ ℝ).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
    let AV := (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
      (c (z, u) • ContinuousLinearMap.snd ℝ ℝ ℝ)
    have hWa : (W z : (ℝ × ℝ) → ℝ × ℝ) =ᶠ[𝓝 (u, 0)]
        (fun x => (x.1 + a (z, x.1) * x.2, x.2)) := by
      have hn : ∀ᶠ x : ℝ × ℝ in 𝓝 (u, 0), |x.2| < r :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hr)
      filter_upwards [hn] with x hx
      exact hWnear z x hx.le
    have hVa : (V z : (ℝ × ℝ) → ℝ × ℝ) =ᶠ[𝓝 (u, 0)]
        (fun x => (x.1, c (z, x.1) * x.2)) := by
      have hn : ∀ᶠ x : ℝ × ℝ in 𝓝 (u, 0), |x.2| < 1 :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by norm_num)
      filter_upwards [hn] with x hx
      exact hVnear z x hx.le
    have hdW : fderiv ℝ (W z) (u, 0) = AW := by
      rw [hWa.fderiv_eq]
      exact ((hasFDerivAt_fst.add (axis_product_hasFDerivAt (fun x => a (z, x))
        (ha.comp (contDiff_const.prodMk contDiff_id)) u)).prodMk hasFDerivAt_snd).fderiv
    have hdV : fderiv ℝ (V z) (u, 0) = AV := by
      rw [hVa.fderiv_eq]
      exact (hasFDerivAt_fst.prodMk (axis_product_hasFDerivAt (fun x => c (z, x))
        (hc.comp (contDiff_const.prodMk contDiff_id)) u)).fderiv
    change fderiv ℝ ((V z) ∘ (W z)) (u, 0) w = _
    rw [fderiv_comp (u, 0) ((V z).contDiff.differentiable (by simp) _)
      ((W z).contDiff.differentiable (by simp) _), hWaxis, hdW, hdV]
    simp [AW, AV, ContinuousLinearMap.comp_apply, smul_eq_mul]
  · intro z hz x
    change V z (W z x) = x
    rw [hWzero z x (hz x.1).1, hVunit z x (hz x.1).2]
  · intro z x hx
    have hf : D z x = x := by
      change V z (W z x) = x
      rw [(hWfix z x (fun h => hx (Or.inr h))).1,
        (hVfix z x (fun h => hx (Or.inl h))).1]
    refine ⟨hf, ?_⟩
    have hh := congrArg (D z).symm hf
    simpa only [(D z).symm_apply_apply] using hh.symm

end PoincareConjecture.M25.Topology3D
