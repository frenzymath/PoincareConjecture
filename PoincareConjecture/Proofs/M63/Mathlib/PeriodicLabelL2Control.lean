import PoincareConjecture.Proofs.M63.Mathlib.PeriodicL2Relabeling
import PoincareConjecture.Proofs.M63.Mathlib.CompactPathDerivative
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.CompactOpen










set_option autoImplicit false

open Set Filter MeasureTheory AddCircle
open scoped Topology ContDiff intervalIntegral

namespace PoincareConjecture.M63





theorem exists_periodicLabel_displacement_L2_control
    {P a b : ℝ} [Fact (0 < P)] (hab : a < b)
    (psi : ℕ → ℝ → ℝ → ℝ) (w : ℕ → ℝ → C(AddCircle P, ℝ))
    (hpsi : ∀ j, ContDiffOn ℝ 1 (Function.uncurry (psi j)) (Icc a b ×ˢ univ))
    (hshift : ∀ j t, t ∈ Icc a b → ∀ x, psi j t (x + P) = psi j t x + P)
    (hw : ∀ j, ContinuousOn (w j) (Ioo a b))
    (htime : ∀ j t, t ∈ Ioo a b → ∀ x,
      HasDerivAt (fun r => psi j r x) (w j t (psi j t x : AddCircle P)) t)
    {ell B : ℝ} (hell : 0 < ell) (hB : 0 ≤ B)
    (hjac : ∀ j t, t ∈ Icc a b → ∀ x, ell ≤ deriv (psi j t) x)
    (hwnorm : ∀ j t, t ∈ Ioo a b →
      ‖ContinuousMap.toLp 2 haarAddCircle ℝ (w j t)‖ ≤ B) :
    ∃ D V : ℕ → ℝ → C(AddCircle P, ℝ),
      (∀ j, ContinuousOn (D j) (Icc a b)) ∧
      (∀ j t, t ∈ Icc a b → ∀ x : ℝ,
        D j t (x : AddCircle P) = psi j t x - x) ∧
      (∀ j, ContinuousOn (V j) (Ioo a b)) ∧
      (∀ j t, t ∈ Ioo a b → ∀ x : ℝ,
        V j t (x : AddCircle P) = w j t (psi j t x : AddCircle P)) ∧
      (∀ j t, t ∈ Ioo a b → HasDerivAt (D j) (V j t) t) ∧
      (∀ j t, t ∈ Ioo a b →
        ‖ContinuousMap.toLp 2 haarAddCircle ℝ (V j t)‖ ≤ Real.sqrt ell⁻¹ * B) ∧
      ∀ j s, s ∈ Icc a b → ∀ t, t ∈ Icc a b →
        ‖ContinuousMap.toLp 2 haarAddCircle ℝ (D j t - D j s)‖ ≤
          Real.sqrt ell⁻¹ * B * |t - s| := by
  classical
  have hP : 0 < P := Fact.out
  have descend (J : Set ℝ) (f : ℝ × ℝ → ℝ)
      (hf : ContinuousOn f (J ×ˢ univ))
      (hp : ∀ t ∈ J, Function.Periodic (fun x => f (t, x)) P) :
      ∃ g : ℝ → C(AddCircle P, ℝ), ContinuousOn g J ∧
        ∀ t ∈ J, ∀ x : ℝ, g t (x : AddCircle P) = f (t, x) := by
    let g : ℝ → C(AddCircle P, ℝ) := fun t => if ht : t ∈ J then
      ⟨(hp t ht).lift,
        (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples P)).continuous_iff.mpr
          (hf.comp_continuous (f := fun x : ℝ => (t, x))
            (continuous_const.prodMk continuous_id) (fun _ => ⟨ht, mem_univ _⟩))⟩ else 0
    have hg (t : ℝ) (ht : t ∈ J) (x : ℝ) : g t (x : AddCircle P) = f (t, x) := by
      simp only [g, dif_pos ht, ContinuousMap.coe_mk, Function.Periodic.lift_coe]
    refine ⟨g, continuousOn_iff_continuous_domRestrict.mpr ?_, hg⟩
    apply ContinuousMap.continuous_of_continuous_uncurry
    have hquot : IsOpenQuotientMap (fun p : J × ℝ => (p.1, (p.2 : AddCircle P))) :=
      IsOpenQuotientMap.id.prodMap QuotientAddGroup.isOpenQuotientMap_mk
    apply hquot.continuous_comp_iff.mp
    have hc : Continuous (fun p : J × ℝ => f (p.1.1, p.2)) :=
      hf.comp_continuous (f := fun p : J × ℝ => (p.1.1, p.2))
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
        (fun p => ⟨p.1.2, mem_univ _⟩)
    exact hc.congr (fun p => (hg p.1.1 p.1.2 p.2).symm)
  have hD (j : ℕ) : ∃ D : ℝ → C(AddCircle P, ℝ),
      ContinuousOn D (Icc a b) ∧
        ∀ t ∈ Icc a b, ∀ x : ℝ, D t (x : AddCircle P) = psi j t x - x := by
    apply descend (Icc a b) (fun z => psi j z.1 z.2 - z.2)
      ((hpsi j).continuousOn.sub continuousOn_snd)
    intro t ht x
    change psi j t (x + P) - (x + P) = psi j t x - x
    rw [hshift j t ht x]
    ring
  have hV (j : ℕ) : ∃ V : ℝ → C(AddCircle P, ℝ),
      ContinuousOn V (Ioo a b) ∧ ∀ t ∈ Ioo a b, ∀ x : ℝ,
        V t (x : AddCircle P) = w j t (psi j t x : AddCircle P) := by
    have hp : ContinuousOn (Function.uncurry (psi j)) (Ioo a b ×ˢ univ) :=
      (hpsi j).continuousOn.mono (prod_mono Ioo_subset_Icc_self Subset.rfl)
    have hpair : ContinuousOn (fun z : ℝ × ℝ =>
        (w j z.1, (psi j z.1 z.2 : AddCircle P))) (Ioo a b ×ˢ univ) :=
      ((hw j).comp continuousOn_fst (fun _ hz => hz.1)).prodMk
        ((AddCircle.continuous_mk' P).comp_continuousOn hp)
    apply descend (Ioo a b) (fun z => w j z.1 (psi j z.1 z.2 : AddCircle P))
      (continuous_eval.comp_continuousOn hpair)
    intro t ht x
    change w j t (psi j t (x + P) : AddCircle P) = w j t (psi j t x : AddCircle P)
    rw [hshift j t (Ioo_subset_Icc_self ht), AddCircle.coe_add_period]
  choose D hDc hDval using hD
  choose V hVc hVval using hV
  have hDder (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) : HasDerivAt (D j) (V j t) t := by
    apply hasDerivAt_compact_curry isOpen_Ioo (D j) (V j) ht
      ((hVc j t ht).continuousAt (isOpen_Ioo.mem_nhds ht))
    intro r hr z
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    rw [hVval j r hr x]
    apply ((htime j r hr x).sub_const x).congr_of_eventuallyEq
    filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
    exact hDval j s (Ioo_subset_Icc_self hs) x
  let T : C(AddCircle P, ℝ) →L[ℝ] Lp ℝ 2 (haarAddCircle (T := P)) :=
    ContinuousMap.toLp 2 haarAddCircle ℝ
  have hnorm (f : C(AddCircle P, ℝ)) :
      ‖T f‖ ^ 2 = ∫ z : AddCircle P, ‖f z‖ ^ 2 ∂haarAddCircle := by
    rw [Lp.norm_def, eLpNorm_congr_ae
      (ContinuousMap.coeFn_toLp (p := 2) haarAddCircle (𝕜 := ℝ) f),
      toReal_eLpNorm (f.memLp (p := 2) (μ := haarAddCircle) ℝ).1,
      lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
        (f.memLp (p := 2) (μ := haarAddCircle) ℝ).1]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, inv_eq_one_div, ← Real.sqrt_eq_rpow]
    exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hperiod (f : C(AddCircle P, ℝ)) :
      Function.Periodic (fun x : ℝ => f (x : AddCircle P)) P := by
    intro x
    change f ((x + P : ℝ) : AddCircle P) = f (x : AddCircle P)
    rw [AddCircle.coe_add_period]
  have hintegral (f : C(AddCircle P, ℝ)) :
      (∫ z : AddCircle P, ‖f z‖ ^ 2 ∂haarAddCircle) =
        P⁻¹ * ∫ x in (0 : ℝ)..P, ‖f (x : AddCircle P)‖ ^ 2 := by
    rw [integral_haarAddCircle, ← AddCircle.intervalIntegral_preimage P 0]
    simp only [zero_add, smul_eq_mul]
  have hpslice (j : ℕ) (t : ℝ) (ht : t ∈ Icc a b) : ContDiff ℝ 1 (psi j t) :=
    (hpsi j).comp_contDiff (f := fun x : ℝ => (t, x))
      (contDiff_const.prodMk contDiff_id) (fun _ => ⟨ht, mem_univ _⟩)
  have hsq (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖T (V j t)‖ ^ 2 ≤ ell⁻¹ * ‖T (w j t)‖ ^ 2 := by
    have hsub := (hperiod (w j t)).integral_norm_sq_comp_le
      ((w j t).continuous.comp (AddCircle.continuous_mk' P)) hP
      (hpslice j t (Ioo_subset_Icc_self ht))
      (hshift j t (Ioo_subset_Icc_self ht)) hell (hjac j t (Ioo_subset_Icc_self ht))
    have heq : (∫ x in (0 : ℝ)..P, ‖V j t (x : AddCircle P)‖ ^ 2) =
        ∫ x in (0 : ℝ)..P, ‖w j t (psi j t x : AddCircle P)‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro x _hx
      change ‖V j t (x : AddCircle P)‖ ^ 2 = ‖w j t (psi j t x : AddCircle P)‖ ^ 2
      rw [hVval j t ht x]
    rw [hnorm, hnorm, hintegral, hintegral, heq]
    calc
      _ ≤ P⁻¹ * (ell⁻¹ * ∫ x in (0 : ℝ)..P, ‖w j t (x : AddCircle P)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hsub (inv_nonneg.mpr hP.le)
      _ = _ := by ring
  have hbound (j : ℕ) (t : ℝ) (ht : t ∈ Ioo a b) :
      ‖T (V j t)‖ ≤ Real.sqrt ell⁻¹ * B := by
    have hcomp : ‖T (V j t)‖ ≤ Real.sqrt ell⁻¹ * ‖T (w j t)‖ := by
      apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
      rw [mul_pow, Real.sq_sqrt (inv_nonneg.mpr hell.le)]
      exact hsq j t ht
    exact hcomp.trans (mul_le_mul_of_nonneg_left (hwnorm j t ht) (Real.sqrt_nonneg _))
  refine ⟨D, V, hDc, hDval, hVc, hVval, hDder, hbound, ?_⟩
  intro j s hs t ht
  let C : NNReal := ⟨Real.sqrt ell⁻¹ * B, mul_nonneg (Real.sqrt_nonneg _) hB⟩
  have hd (r : ℝ) (hr : r ∈ Ioo a b) :
      HasDerivAt (fun u => T (D j u)) (T (V j r)) r :=
    T.hasFDerivAt.comp_hasDerivAt r (hDder j r hr)
  have hopen : LipschitzOnWith C (fun u => T (D j u)) (Ioo a b) :=
    (convex_Ioo a b).lipschitzOnWith_of_nnnorm_deriv_le
      (fun r hr => (hd r hr).differentiableAt) (fun r hr => by
        change ‖deriv (fun u => T (D j u)) r‖ ≤ Real.sqrt ell⁻¹ * B
        rw [(hd r hr).deriv]
        exact hbound j r hr)
  have hclosed : ContinuousOn (fun u => T (D j u)) (closure (Ioo a b)) := by
    rw [closure_Ioo hab.ne]
    exact T.continuous.comp_continuousOn (hDc j)
  have hclosure : LipschitzOnWith C (fun u => T (D j u)) (Icc a b) := by
    simpa only [closure_Ioo hab.ne] using LipschitzOnWith.closure hclosed hopen
  change ‖T (D j t - D j s)‖ ≤ (C : ℝ) * |t - s|
  simpa only [map_sub, dist_eq_norm, Real.norm_eq_abs] using hclosure.dist_le_mul t ht s hs

end PoincareConjecture.M63
