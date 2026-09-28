import PoincareConjecture.Proofs.M63.Mathlib.CompactPathDerivative
import PoincareConjecture.Proofs.M63.Mathlib.PeriodicTranslationSmoothness
import PoincareConjecture.Proofs.M63.Sec19_1_LocalFlow.PeriodicGaussianGradient
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open Set Filter MeasureTheory
open scoped Topology intervalIntegral

namespace PoincareConjecture.M63

variable {L : ℝ} [Fact (0 < L)]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuous_periodicGaussianHeat_action :
    Continuous (fun p : ℝ × C(AddCircle L, E) => periodicGaussianHeat p.1 p.2) := by
  apply continuous_prod_of_continuous_lipschitzWith' _ 1
  · intro t
    apply LipschitzWith.of_dist_le_mul
    intro f g
    rw [dist_eq_norm, ← map_sub, NNReal.coe_one, one_mul, dist_eq_norm]
    exact (periodicGaussianHeat_properties (f - g)).1 t
  · intro f
    exact (periodicGaussianHeat_properties f).2.2

theorem hasDerivAt_periodicGaussianHeat_backward
    {a b ν : ℝ} (_hab : a ≤ b) (hν : 0 < ν)
    (h h₁ h₂ hdot : ℝ → C(AddCircle L, E))
    (_hh : ContinuousOn h (Icc a b)) (hh₁ : ContinuousOn h₁ (Icc a b))
    (_hh₂ : ContinuousOn h₂ (Icc a b)) (hhdot : ContinuousOn hdot (Icc a b))
    (hx : ∀ s ∈ Icc a b, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h s (y : AddCircle L)) (h₁ s (x : AddCircle L)) x)
    (hxx : ∀ s ∈ Icc a b, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h₁ s (y : AddCircle L)) (h₂ s (x : AddCircle L)) x)
    (htime : ∀ s ∈ Ioo a b, ∀ x : ℝ,
      HasDerivAt (fun r => h r (x : AddCircle L)) (hdot s (x : AddCircle L)) s)
    {t r : ℝ} (ht : t ∈ Icc a b) (hr : r ∈ Ioo a t) (x : ℝ) :
    HasDerivAt (fun s => periodicGaussianHeat (ν * (t - s)) (h s) (x : AddCircle L))
      (periodicGaussianHeat (ν * (t - r)) (hdot r - ν • h₂ r) (x : AddCircle L)) r := by
  let X := C(AddCircle L, E)
  let S : Set (ℝ × ℝ) := Ioo a b ×ˢ univ
  have hS : IsOpen S := isOpen_Ioo.prod isOpen_univ
  have htimeX (s : ℝ) (hs : s ∈ Ioo a b) : HasDerivAt h (hdot s) s := by
    apply hasDerivAt_compact_curry isOpen_Ioo h hdot hs
      (hhdot.continuousAt (Icc_mem_nhds hs.1 hs.2))
    intro u hu z
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective z
    exact htime u hu z
  have hjoint (s : ℝ) (hs : s ∈ Ioo a b) (z : ℝ) :
      HasFDerivAt (fun p : ℝ × ℝ => periodicTranslation p.2 (h p.1))
        ((ContinuousLinearMap.toSpanSingleton ℝ (periodicTranslation z (hdot s))).coprod
          (ContinuousLinearMap.toSpanSingleton ℝ (-(periodicTranslation z (h₁ s)))))
        (s, z) := by
    have hmem : ∀ᶠ p in 𝓝 (s, z), p ∈ S := hS.mem_nhds ⟨hs, mem_univ _⟩
    have hd₁ : ∀ᶠ p in 𝓝 (s, z),
        HasFDerivAt (fun u => periodicTranslation p.2 (h u))
          (ContinuousLinearMap.toSpanSingleton ℝ (periodicTranslation p.2 (hdot p.1)))
          p.1 := by
      filter_upwards [hmem] with p hp
      let T : X →L[ℝ] X := (periodicTranslation p.2).toContinuousLinearEquiv.toContinuousLinearMap
      exact (T.hasFDerivAt.comp_hasDerivAt p.1 (htimeX p.1 hp.1)).hasFDerivAt
    have hd₂ : ∀ᶠ p in 𝓝 (s, z),
        HasFDerivAt (fun u => periodicTranslation u (h p.1))
          (ContinuousLinearMap.toSpanSingleton ℝ (-(periodicTranslation p.2 (h₁ p.1))))
          p.2 := by
      filter_upwards [hmem] with p hp
      exact (hasDerivAt_periodicTranslation (h p.1) (h₁ p.1)
        (hx p.1 (Ioo_subset_Icc_self hp.1)) p.2).hasFDerivAt
    have hc₁ : ContinuousAt
        (fun p : ℝ × ℝ => periodicTranslation p.2 (hdot p.1)) (s, z) :=
      continuous_periodicTranslation.continuousAt.comp
        (continuousAt_snd.prodMk
          ((hhdot.continuousAt (Icc_mem_nhds hs.1 hs.2)).comp continuousAt_fst))
    have hc₂ : ContinuousAt
        (fun p : ℝ × ℝ => -(periodicTranslation p.2 (h₁ p.1))) (s, z) :=
      (continuous_periodicTranslation.continuousAt.comp
        (continuousAt_snd.prodMk
          ((hh₁.continuousAt (Icc_mem_nhds hs.1 hs.2)).comp continuousAt_fst))).neg
    exact (hasStrictFDerivAt_uncurry_coprod
      (f := fun u v => periodicTranslation v (h u))
      (f₁ := fun u v => ContinuousLinearMap.toSpanSingleton ℝ (periodicTranslation v (hdot u)))
      (f₂ := fun u v => ContinuousLinearMap.toSpanSingleton ℝ (-(periodicTranslation v (h₁ u))))
      hd₁ hd₂
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ X).continuous.continuousAt.comp hc₁)
      ((ContinuousLinearMap.toSpanSingletonLIE ℝ X).continuous.continuousAt.comp hc₂)).hasFDerivAt
  let K : ℝ → ℝ := gaussianHeatKernel 1
  let Q (s z : ℝ) : X := K z • periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (h s)
  let Q' (s z : ℝ) : X := K z •
    (periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (hdot s) +
      (ν * z / Real.sqrt (ν * (t - s))) •
        periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (h₁ s))
  let η := ν * (t - r) / 2
  let N : Set ℝ := Ioo a ((r + t) / 2)
  have hη : 0 < η := div_pos (mul_pos hν (sub_pos.mpr hr.2)) (by norm_num)
  have hN : N ∈ 𝓝 r := Ioo_mem_nhds hr.1 (by linarith [hr.2])
  have hNs (s : ℝ) (hs : s ∈ N) : s ∈ Ioo a b :=
    ⟨hs.1, by dsimp [N] at hs; linarith [hs.2, hr.2, ht.2]⟩
  have hlag (s : ℝ) (hs : s ∈ N) : η ≤ ν * (t - s) := by
    dsimp [η, N] at *
    nlinarith [hs.2]
  have hdQ (z s : ℝ) (hs : s ∈ N) : HasDerivAt (fun u => Q u z) (Q' s z) s := by
    have hτ : 0 < ν * (t - s) := hη.trans_le (hlag s hs)
    have hσ : HasDerivAt (fun u : ℝ => 2 * Real.sqrt (ν * (t - u)) * z)
        (-(ν * z / Real.sqrt (ν * (t - s)))) s := by
      have hd₀ := ((((hasDerivAt_id s).const_sub t).const_mul ν).sqrt hτ.ne').const_mul 2
      have hd := hd₀.mul_const z
      apply hd.congr_deriv
      simp only [id_eq]
      field_simp
    have hd := (hjoint s (hNs s hs) (2 * Real.sqrt (ν * (t - s)) * z)).comp_hasDerivAt s
      ((hasDerivAt_id s).prodMk hσ)
    have hd' : HasDerivAt
        (fun u => periodicTranslation (2 * Real.sqrt (ν * (t - u)) * z) (h u))
        (periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (hdot s) +
          (ν * z / Real.sqrt (ν * (t - s))) •
            periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (h₁ s)) s := by
      simpa only [Function.comp_def, id_eq, ContinuousLinearMap.coprod_apply,
        ContinuousLinearMap.toSpanSingleton_apply, one_smul, neg_smul, smul_neg, neg_neg] using! hd
    exact hd'.fun_const_smul (K z)
  obtain ⟨Ct, hCt⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hhdot
  obtain ⟨Cx, hCx⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hh₁
  have hrab : r ∈ Icc a b := ⟨hr.1.le, hr.2.le.trans ht.2⟩
  have hCt0 : 0 ≤ Ct := (norm_nonneg (hdot r)).trans (hCt r hrab)
  have hCx0 : 0 ≤ Cx := (norm_nonneg (h₁ r)).trans (hCx r hrab)
  have hK : Integrable K :=
    (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul _
  have hzK : Integrable (fun z : ℝ => z * K z) := by
    convert! (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).const_mul
      ((Real.sqrt (Real.pi / 1))⁻¹) using 1
    funext z
    dsimp only [K, gaussianHeatKernel]
    ring
  have habsK : Integrable (fun z : ℝ => |z| * K z) := by
    convert! hzK.norm using 1
    funext z
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (gaussianHeatKernel_pos (by norm_num) z)]
  have hmajorant : Integrable (fun z : ℝ => K z * (Ct + (ν / Real.sqrt η) * |z| * Cx)) := by
    convert! (hK.mul_const Ct).add (habsK.mul_const ((ν / Real.sqrt η) * Cx)) using 1
    funext z
    simp only [Pi.add_apply]
    ring
  have hbound (z s : ℝ) (hs : s ∈ N) :
      ‖Q' s z‖ ≤ K z * (Ct + (ν / Real.sqrt η) * |z| * Cx) := by
    have hτ : 0 < ν * (t - s) := hη.trans_le (hlag s hs)
    have hsqrt : 0 < Real.sqrt (ν * (t - s)) := Real.sqrt_pos.mpr hτ
    have hc : |ν * z / Real.sqrt (ν * (t - s))| ≤ (ν / Real.sqrt η) * |z| := by
      rw [abs_div, abs_mul, abs_of_pos hν, abs_of_pos hsqrt]
      calc
        _ ≤ (ν * |z|) / Real.sqrt η :=
          div_le_div_of_nonneg_left (mul_nonneg hν.le (abs_nonneg z))
            (Real.sqrt_pos.mpr hη) (Real.sqrt_le_sqrt (hlag s hs))
        _ = _ := by ring
    dsimp only [Q']
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (gaussianHeatKernel_pos (by norm_num) z)]
    apply mul_le_mul_of_nonneg_left _ (gaussianHeatKernel_pos (by norm_num) z).le
    calc
      _ ≤ ‖periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (hdot s)‖ +
          ‖(ν * z / Real.sqrt (ν * (t - s))) •
            periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) (h₁ s)‖ := norm_add_le _ _
      _ = ‖hdot s‖ + |ν * z / Real.sqrt (ν * (t - s))| * ‖h₁ s‖ := by
        rw [norm_smul, Real.norm_eq_abs, (periodicTranslation _).norm_map,
          (periodicTranslation _).norm_map]
      _ ≤ Ct + ((ν / Real.sqrt η) * |z|) * Cx :=
        add_le_add (hCt s (Ioo_subset_Icc_self (hNs s hs)))
          (mul_le_mul hc (hCx s (Ioo_subset_Icc_self (hNs s hs))) (norm_nonneg _) (by positivity))
      _ = _ := by ring
  have hKc : Continuous K :=
    continuous_iff_continuousAt.mpr fun _ => gaussianHeatKernel_hasDerivAt.continuousAt
  have htrans (f : X) (s : ℝ) : Continuous
      (fun z : ℝ => periodicTranslation (2 * Real.sqrt (ν * (t - s)) * z) f) :=
    continuous_periodicTranslation.comp
      ((continuous_const.mul continuous_id).prodMk continuous_const)
  have hQ'c : Continuous (Q' r) := hKc.smul
    ((htrans (hdot r) r).add
      (((continuous_const.mul continuous_id).div_const _).smul (htrans (h₁ r) r)))
  have hint := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := Q) (F' := Q') (x₀ := r) (s := N)
    (bound := fun z : ℝ => K z * (Ct + (ν / Real.sqrt η) * |z| * Cx)) hN
    (Eventually.of_forall fun s =>
      (integrable_periodicGaussian (ν * (t - s)) (h s)).aestronglyMeasurable)
    (integrable_periodicGaussian (ν * (t - r)) (h r)) hQ'c.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun z s hs => hbound z s hs) hmajorant
    (Eventually.of_forall fun z s hs => hdQ z s hs)
  let τ := ν * (t - r)
  let A := 2 * Real.sqrt τ
  have hτ : 0 < τ := mul_pos hν (sub_pos.mpr hr.2)
  have hA : 0 < A := by dsimp [A]; positivity
  let J₁ : X := ∫ z : ℝ, ((-2 * z) * K z) • periodicTranslation (A * z) (h₁ r)
  have hfirst : periodicGaussianHeat τ (h₂ r) = A⁻¹ • J₁ := by
    ext y
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
    change periodicGaussianHeat τ (h₂ r) (y : AddCircle L) =
      A⁻¹ • (ContinuousMap.evalCLM ℝ (y : AddCircle L)) J₁
    dsimp only [J₁]
    rw [← (ContinuousMap.evalCLM ℝ (y : AddCircle L)).integral_comp_comm
      (integrable_periodicGaussianFirstKernel τ (h₁ r))]
    exact (periodicGaussianHeat_derivative_formula_bound hτ (h₁ r) (h₂ r) (hxx r hrab)).1 y
  have hsplit (z : ℝ) : Q' r z = K z • periodicTranslation (A * z) (hdot r) +
      (-ν / A) • (((-2 * z) * K z) • periodicTranslation (A * z) (h₁ r)) := by
    dsimp only [Q', A, τ]
    rw [smul_add, smul_smul, smul_smul]
    congr 1
    congr 1
    field_simp
  have hvalue : (∫ z : ℝ, Q' r z) = periodicGaussianHeat τ (hdot r - ν • h₂ r) := by
    have hi₀ : Integrable (fun z : ℝ => K z • periodicTranslation (A * z) (hdot r)) :=
      integrable_periodicGaussian τ (hdot r)
    have hi₁ : Integrable (fun z : ℝ =>
        (-ν / A) • (((-2 * z) * K z) • periodicTranslation (A * z) (h₁ r))) :=
      (integrable_periodicGaussianFirstKernel τ (h₁ r)).smul (-ν / A)
    simp_rw [hsplit]
    rw [integral_add hi₀ hi₁, integral_smul]
    change periodicGaussianHeat τ (hdot r) + (-ν / A) • J₁ = _
    rw [map_sub, map_smul, hfirst, smul_smul, sub_eq_add_neg, ← neg_smul]
    congr 1
    congr 1
    ring
  have hd : HasDerivAt (fun s => periodicGaussianHeat (ν * (t - s)) (h s))
      (periodicGaussianHeat τ (hdot r - ν • h₂ r)) r := hint.2.congr_deriv hvalue
  exact (ContinuousMap.evalCLM ℝ (x : AddCircle L)).hasFDerivAt.comp_hasDerivAt r hd

theorem periodicGaussianHeat_duhamel_of_derivative_witnesses
    {a b ν : ℝ} (hab : a ≤ b) (hν : 0 < ν)
    (h h₁ h₂ hdot : ℝ → C(AddCircle L, E))
    (hh : ContinuousOn h (Icc a b)) (hh₁ : ContinuousOn h₁ (Icc a b))
    (hh₂ : ContinuousOn h₂ (Icc a b)) (hhdot : ContinuousOn hdot (Icc a b))
    (hx : ∀ s ∈ Icc a b, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h s (y : AddCircle L)) (h₁ s (x : AddCircle L)) x)
    (hxx : ∀ s ∈ Icc a b, ∀ x : ℝ,
      HasDerivAt (fun y : ℝ => h₁ s (y : AddCircle L)) (h₂ s (x : AddCircle L)) x)
    (htime : ∀ s ∈ Ioo a b, ∀ x : ℝ,
      HasDerivAt (fun r => h r (x : AddCircle L)) (hdot s (x : AddCircle L)) s)
    {t : ℝ} (ht : t ∈ Icc a b) :
    h t = periodicGaussianHeat (ν * (t - a)) (h a) +
      ∫ r in a..t, periodicGaussianHeat (ν * (t - r)) (hdot r - ν • h₂ r) := by
  let R (r : ℝ) := periodicGaussianHeat (ν * (t - r)) (hdot r - ν • h₂ r)
  have hlag : Continuous (fun r : ℝ => ν * (t - r)) :=
    continuous_const.mul (continuous_const.sub continuous_id)
  have hpath : ContinuousOn (fun r => periodicGaussianHeat (ν * (t - r)) (h r)) (Icc a t) := by
    have hp : ContinuousOn (fun r : ℝ => (ν * (t - r), h r)) (Icc a t) :=
      hlag.continuousOn.prodMk (hh.mono (Icc_subset_Icc_right ht.2))
    have hcomp := (continuous_periodicGaussianHeat_action (L := L) (E := E)).comp_continuousOn
      (s := Icc a t) hp
    exact hcomp
  have hR : ContinuousOn R (Icc a t) := by
    have hp : ContinuousOn
        (fun r : ℝ => (ν * (t - r), hdot r - ν • h₂ r)) (Icc a t) :=
      hlag.continuousOn.prodMk
        ((hhdot.sub (hh₂.const_smul ν)).mono (Icc_subset_Icc_right ht.2))
    have hcomp := (continuous_periodicGaussianHeat_action (L := L) (E := E)).comp_continuousOn
      (s := Icc a t) hp
    exact hcomp
  have hRi : IntervalIntegrable R volume a t := hR.intervalIntegrable_of_Icc ht.1
  ext x
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective x
  let ev : C(AddCircle L, E) →L[ℝ] E := ContinuousMap.evalCLM ℝ (x : AddCircle L)
  have hpoint := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1
    (ev.continuous.comp_continuousOn hpath)
    (fun r hr => hasDerivAt_periodicGaussianHeat_backward hab hν h h₁ h₂ hdot
      hh hh₁ hh₂ hhdot hx hxx htime ht hr x)
    ((ev.continuous.comp_continuousOn hR).intervalIntegrable_of_Icc ht.1)
  have hi : (∫ r in a..t, R r) (x : AddCircle L) =
      h t (x : AddCircle L) - periodicGaussianHeat (ν * (t - a)) (h a) (x : AddCircle L) := by
    change ev (∫ r in a..t, R r) = _
    rw [← ev.intervalIntegral_comp_comm hRi]
    change (∫ r in a..t, ev (R r)) =
      ev (periodicGaussianHeat (ν * (t - t)) (h t)) -
        ev (periodicGaussianHeat (ν * (t - a)) (h a)) at hpoint
    simpa only [sub_self, mul_zero, (periodicGaussianHeat_properties (h t)).2.1] using! hpoint
  change h t (x : AddCircle L) =
    periodicGaussianHeat (ν * (t - a)) (h a) (x : AddCircle L) +
      (∫ r in a..t, R r) (x : AddCircle L)
  rw [hi]
  abel

end PoincareConjecture.M63
