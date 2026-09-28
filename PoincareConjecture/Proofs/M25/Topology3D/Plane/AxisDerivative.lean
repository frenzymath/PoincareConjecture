import PoincareConjecture.Proofs.M25.Topology3D.Plane.AxisPointwiseCorrection
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Topology.Order.Compact

set_option autoImplicit false

open Set Function
open scoped ContDiff Manifold Topology

namespace PoincareConjecture.M25.Topology3D

private theorem fderiv_eq_id_off_compact (f : (ℝ × ℝ) → ℝ × ℝ)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → f x = x) {x : ℝ × ℝ} (hx : x ∉ K) :
    fderiv ℝ f x = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
  have heq : f =ᶠ[𝓝 x] id := by
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hx] with y hy
    exact hfix y hy
  rw [heq.fderiv_eq, fderiv_id]

theorem fderiv_fixed_axis_horizontal (f : (ℝ × ℝ) → ℝ × ℝ)
    (hf : Differentiable ℝ f) (hfix : ∀ u, f (u, 0) = (u, 0)) (u : ℝ) :
    fderiv ℝ f (u, 0) (1, 0) = (1, 0) := by
  have hline : HasDerivAt (fun s : ℝ => (s, (0 : ℝ))) (1, 0) u :=
    (hasDerivAt_id u).prodMk (hasDerivAt_const u (0 : ℝ))
  have hd := (hf (u, 0)).hasFDerivAt.comp_hasDerivAt u hline
  have heq : f ∘ (fun s : ℝ => (s, (0 : ℝ))) = (fun s => (s, (0 : ℝ))) :=
    funext hfix
  rw [heq] at hd
  exact hd.unique hline

theorem normal_fderiv_pos_of_fixed_axis (F : (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ x, x ∉ K → F x = x) (haxis : ∀ u, F (u, 0) = (u, 0))
    (u : ℝ) : 0 < (fderiv ℝ F (u, 0) (0, 1)).2 := by
  let c : ℝ → ℝ := fun s => (fderiv ℝ F (s, 0) (0, 1)).2
  have hD : ContDiff ℝ ∞ (fderiv ℝ F) := F.contDiff.fderiv_right (by simp)
  have hc : ContDiff ℝ ∞ c :=
    ((hD.comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const).snd
  have hne (s : ℝ) : c s ≠ 0 := by
    let A := fderiv ℝ F (s, 0)
    have hcomp : (fderiv ℝ F.symm (F (s, 0))).comp A =
        ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
      rw [← fderiv_comp (s, 0) (F.symm.contDiff.differentiable (by simp) _)
        (F.contDiff.differentiable (by simp) _)]
      have heq : (F.symm : (ℝ × ℝ) → ℝ × ℝ) ∘ F = id :=
        funext F.symm_apply_apply
      rw [heq, fderiv_id]
    have hi : Injective A := by
      intro v w hvw
      have hh := congrArg (fderiv ℝ F.symm (F (s, 0))) hvw
      simpa only [← ContinuousLinearMap.comp_apply, hcomp,
        ContinuousLinearMap.id_apply] using hh
    have hhor : A (1, 0) = (1, 0) :=
      fderiv_fixed_axis_horizontal F (F.contDiff.differentiable (by simp)) haxis s
    intro hz
    let a := (A (0, 1)).1
    have heq : A (0, 1) = a • ((1, 0) : ℝ × ℝ) := by
      apply Prod.ext
      · simp [a]
      · simpa [c, A] using hz
    have hh : A (((0, 1) : ℝ × ℝ) - a • (1, 0)) = A 0 := by
      rw [map_sub, map_smul, hhor, heq, sub_self, map_zero]
    have hv := congrArg (Prod.snd : ℝ × ℝ → ℝ) (hi hh)
    norm_num at hv
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  let v := max R u + 1
  have hvR : R < v := by dsimp [v]; linarith [le_max_left R u]
  have huv : u < v := by dsimp [v]; linarith [le_max_right R u]
  have hvK : (v, (0 : ℝ)) ∉ K := by
    intro hv
    have hh := (norm_fst_le (v, (0 : ℝ))).trans_lt (hbound _ hv)
    rw [Real.norm_eq_abs, abs_of_pos (hR.trans hvR)] at hh
    exact (not_lt_of_ge hvR.le) hh
  have hcv : c v = 1 := by
    dsimp only [c]
    rw [fderiv_eq_id_off_compact F hK hfix hvK]
    rfl
  change 0 < c u
  by_contra hn
  have hzero : (0 : ℝ) ∈ Icc (c u) (c v) := ⟨le_of_not_gt hn, by rw [hcv]; norm_num⟩
  obtain ⟨w, _, hw⟩ := intermediate_value_Icc huv.le hc.continuous.continuousOn hzero
  exact hne w hw

theorem exists_fixed_axis_derivative_coefficients
    (F : ℝ → (ℝ × ℝ) ≃ₘ[ℝ] (ℝ × ℝ))
    (hF : ContDiff ℝ ∞ (fun p : ℝ × (ℝ × ℝ) => F p.1 p.2))
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hfix : ∀ z x, x ∉ K → F z x = x)
    (haxis : ∀ z u, F z (u, 0) = (u, 0)) {ε : ℝ} (hε : 0 < ε)
    (hstrip : ∀ z, z ≤ 0 ∨ 1 ≤ z → ∀ x : ℝ × ℝ, |x.2| < ε → F z x = x) :
    ∃ (a c : ℝ × ℝ → ℝ) (R m M : ℝ), 0 < R ∧ 0 < m ∧
      ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ c ∧
      (∀ z u w, fderiv ℝ (F z) (u, 0) w =
        (w.1 + a (z, u) * w.2, c (z, u) * w.2)) ∧
      (∀ p, m ≤ c p ∧ c p ≤ M) ∧
      (∀ z u, z ≤ 0 ∨ 1 ≤ z → a (z, u) = 0 ∧ c (z, u) = 1) ∧
      (∀ z u, R ≤ |u| → a (z, u) = 0 ∧ c (z, u) = 1) ∧
      HasCompactSupport a ∧ HasCompactSupport (fun p => c p - 1) := by
  let V : ℝ × ℝ → ℝ × ℝ := fun p => fderiv ℝ (F p.1) (p.2, 0) (0, 1)
  have hunc : ContDiff ℝ ∞ (fun q : (ℝ × ℝ) × (ℝ × ℝ) => F q.1.1 q.2) :=
    hF.comp (contDiff_fst.fst.prodMk contDiff_snd)
  have hV : ContDiff ℝ ∞ V := hunc.fderiv_apply
    (contDiff_snd.prodMk contDiff_const) contDiff_const (by simp)
  let a : ℝ × ℝ → ℝ := fun p => (V p).1
  let c : ℝ × ℝ → ℝ := fun p => (V p).2
  have ha : ContDiff ℝ ∞ a := hV.fst
  have hc : ContDiff ℝ ∞ c := hV.snd
  have hpos (p : ℝ × ℝ) : 0 < c p :=
    normal_fderiv_pos_of_fixed_axis (F p.1) hK (hfix p.1) (haxis p.1) p.2
  have hformula (z u : ℝ) (w : ℝ × ℝ) : fderiv ℝ (F z) (u, 0) w =
      (w.1 + a (z, u) * w.2, c (z, u) * w.2) := by
    have hw : w = w.1 • ((1, 0) : ℝ × ℝ) + w.2 • ((0, 1) : ℝ × ℝ) := by
      ext <;> simp
    conv_lhs => rw [hw, map_add, map_smul, map_smul,
      fderiv_fixed_axis_horizontal (F z) ((F z).contDiff.differentiable (by simp))
        (haxis z) u]
    ext <;> simp [a, c, V, mul_comm]
  obtain ⟨R, hR, hbound⟩ := hK.isBounded.exists_pos_norm_lt
  have hspace (z u : ℝ) (hu : R ≤ |u|) : a (z, u) = 0 ∧ c (z, u) = 1 := by
    have huK : (u, (0 : ℝ)) ∉ K := by
      intro hp
      have hh := (norm_fst_le (u, (0 : ℝ))).trans_lt (hbound _ hp)
      rw [Real.norm_eq_abs] at hh
      exact (not_lt_of_ge hu) hh
    have hd := fderiv_eq_id_off_compact (F z) hK (hfix z) huK
    simp [a, c, V, hd]
  have htime (z u : ℝ) (hz : z ≤ 0 ∨ 1 ≤ z) : a (z, u) = 0 ∧ c (z, u) = 1 := by
    have heq : (F z : (ℝ × ℝ) → ℝ × ℝ) =ᶠ[𝓝 (u, 0)] id := by
      have hn : ∀ᶠ x : ℝ × ℝ in 𝓝 (u, 0), |x.2| < ε :=
        (isOpen_lt continuous_snd.abs continuous_const).mem_nhds (by simpa using hε)
      filter_upwards [hn] with x hx
      exact hstrip z hz x hx
    have hd : fderiv ℝ (F z) (u, 0) = ContinuousLinearMap.id ℝ (ℝ × ℝ) := by
      rw [heq.fderiv_eq, fderiv_id]
    simp [a, c, V, hd]
  let J : Set (ℝ × ℝ) := Icc 0 1 ×ˢ Icc (-R) R
  have hJ : IsCompact J := isCompact_Icc.prod isCompact_Icc
  have hout (p : ℝ × ℝ) (hp : p ∉ J) : a p = 0 ∧ c p = 1 := by
    by_cases ht : p.1 ≤ 0 ∨ 1 ≤ p.1
    · exact htime p.1 p.2 ht
    · apply hspace
      by_contra hs
      have hh := abs_lt.mp (lt_of_not_ge hs)
      exact hp ⟨⟨(lt_of_not_ge (not_or.mp ht).1).le,
        (lt_of_not_ge (not_or.mp ht).2).le⟩, ⟨hh.1.le, hh.2.le⟩⟩
  obtain ⟨m, hm, hmin⟩ := hJ.exists_forall_le' hc.continuous.continuousOn
    (fun p _ => hpos p)
  obtain ⟨M, _, hmax⟩ := (hJ.image hc.continuous).isBounded.exists_pos_norm_lt
  refine ⟨a, c, R, min m 1, max M 1, hR, lt_min hm zero_lt_one, ha, hc,
    hformula, ?_, htime, hspace, HasCompactSupport.intro hJ (fun p hp => (hout p hp).1),
    HasCompactSupport.intro hJ (fun p hp => sub_eq_zero.mpr (hout p hp).2)⟩
  intro p
  by_cases hp : p ∈ J
  · refine ⟨(min_le_left m 1).trans (hmin p hp), ?_⟩
    have hh := hmax (c p) ⟨p, hp, rfl⟩
    rw [Real.norm_eq_abs] at hh
    exact ((le_abs_self (c p)).trans hh.le).trans (le_max_left M 1)
  · rw [(hout p hp).2]
    exact ⟨min_le_right m 1, le_max_right M 1⟩

end PoincareConjecture.M25.Topology3D
