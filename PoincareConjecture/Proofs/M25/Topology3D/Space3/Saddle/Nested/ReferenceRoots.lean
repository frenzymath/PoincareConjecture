import PoincareConjecture.Proofs.M25.Topology3D.Space3.Saddle.NestedLowerEstimates
import Mathlib.Analysis.Calculus.ImplicitContDiff

set_option autoImplicit false

open Set Metric Filter
open scoped ContDiff Manifold NNReal Topology

namespace PoincareConjecture.M25.Topology3D.NestedReferenceLower

theorem exists_smooth_roots_in_height_window :
    let I : Set ℝ := Ioo (-3 / 2) (3 / 2)
    let J : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
    let r0 : ℝ := Real.sqrt 15 / 4
    let r1 : ℝ := Real.sqrt 4095 / 64
    let U : ℝ → ℝ → ℝ := fun t r =>
      r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t / 32
    let D : ℝ → ℝ → ℝ := fun t r =>
      2 * r - r / Real.sqrt (1 - r ^ 2) + t / 32
    ∃ ri ro : ℝ × ℝ → ℝ,
      ContDiffOn ℝ ∞ ri (I ×ˢ J) ∧ ContDiffOn ℝ ∞ ro (I ×ˢ J) ∧
      ∀ p ∈ I ×ˢ J,
        1 / 4 < ri p ∧ ri p < 1 / 2 ∧
        r0 < ro p ∧ ro p < r1 ∧
        U p.1 (ri p) = p.2 ∧ U p.1 (ro p) = p.2 ∧
        (∀ r ∈ Icc (0 : ℝ) 1,
          (U p.1 r = p.2 ↔ r = ri p ∨ r = ro p) ∧
          (U p.1 r < p.2 ↔ r < ri p ∨ ro p < r) ∧
          (p.2 < U p.1 r ↔ ri p < r ∧ r < ro p) ∧
          (p.2 ≤ U p.1 r ↔ ri p ≤ r ∧ r ≤ ro p)) ∧
        17 / 320 < D p.1 (ri p) ∧ D p.1 (ro p) < -93 / 64 ∧
        HasDerivAt (fun h : ℝ => ri (p.1, h)) (D p.1 (ri p))⁻¹ p.2 ∧
        HasDerivAt (fun h : ℝ => ro (p.1, h)) (D p.1 (ro p))⁻¹ p.2 := by
  classical
  let J : Set ℝ := Ioo (17 / 16 - 1 / 8192) (17 / 16 + 1 / 8192)
  let I : Set (ℝ × ℝ) := Ioo (-3 / 2 : ℝ) (3 / 2) ×ˢ J
  let r0 : ℝ := Real.sqrt 15 / 4
  let r1 : ℝ := Real.sqrt 4095 / 64
  let U : (ℝ × ℝ) → ℝ → ℝ := fun t r =>
    r ^ 2 + Real.sqrt (1 - r ^ 2) + r * t.1 / 32
  let D : (ℝ × ℝ) → ℝ → ℝ := fun t r =>
    2 * r - r / Real.sqrt (1 - r ^ 2) + t.1 / 32
  change ∃ ri ro : ℝ × ℝ → ℝ, ContDiffOn ℝ ∞ ri I ∧ ContDiffOn ℝ ∞ ro I ∧ _
  obtain ⟨hr0, hr01, hr1, hU0, hD0, hE0⟩ := radial_estimates
  change 3 / 4 < r0 at hr0
  change r0 < r1 at hr01
  change r1 < 1 at hr1
  have hU : ContDiffOn ℝ ∞
      (fun p : (ℝ × ℝ) × ℝ => U p.1 p.2 - p.1.2)
      (univ ×ˢ Ioo (-1 : ℝ) 1) := by
    have harg : ContDiff ℝ ∞ (fun p : (ℝ × ℝ) × ℝ => (p.1.1, p.2)) :=
      contDiff_fst.fst.prodMk contDiff_snd
    exact (hU0.comp harg.contDiffOn (fun _ hp => ⟨mem_univ _, hp.2⟩)).sub
      contDiff_fst.snd.contDiffOn
  have hD (t : ℝ × ℝ) (r : ℝ) (hr : r ∈ Ioo (-1 : ℝ) 1) :
      HasDerivAt (U t) (D t r) r := hD0 t.1 r hr
  have hE (t : ℝ × ℝ) (ht : t ∈ I) :
      (∀ r ∈ Icc (0 : ℝ) (1 / 4), U t r < 267 / 256) ∧
      137 / 128 < U t (1 / 2) ∧
      (∀ r ∈ Icc (1 / 4 : ℝ) (3 / 4), 17 / 320 < D t r) ∧
      StrictMonoOn (U t) (Icc (1 / 4 : ℝ) (3 / 4)) ∧
      (∀ r ∈ Icc (3 / 4 : ℝ) r0, 73 / 64 < U t r) ∧
      (∀ r ∈ Ico r0 (1 : ℝ), D t r < -93 / 64) ∧
      StrictAntiOn (U t) (Icc r0 (1 : ℝ)) ∧ U t r1 < 4351 / 4096 :=
    hE0 t.1 ht.1
  have hBounds (t : ℝ × ℝ) (ht : t ∈ I) :
      267 / 256 < t.2 ∧ t.2 < 137 / 128 ∧
        t.2 < 73 / 64 ∧ 4351 / 4096 < t.2 := by
    have hlo : 17 / 16 - 1 / 8192 < t.2 := ht.2.1
    have hhi : t.2 < 17 / 16 + 1 / 8192 := ht.2.2
    constructor
    · linarith
    constructor
    · linarith
    constructor <;> linarith
  have hC (t : ℝ × ℝ) : Continuous (U t) :=
    ((continuous_id.pow 2).add
      (Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2)))).add
      ((continuous_id.mul continuous_const).div_const 32)
  have hInner (t : ℝ × ℝ) (ht : t ∈ I) :
      ∃ r ∈ Ioo (1 / 4 : ℝ) (1 / 2), U t r = t.2 := by
    have he := hE t ht
    have hlo : U t (1 / 4) < t.2 := by
      have hh := he.1 (1 / 4) ⟨by norm_num, le_rfl⟩
      linarith only [hh, (hBounds t ht).1, (hBounds t ht).2.2.1]
    have hhi : t.2 < U t (1 / 2) := by linarith only [he.2.1, (hBounds t ht).2.1]
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc
      (show (1 / 4 : ℝ) ≤ 1 / 2 by norm_num) (hC t).continuousOn
      (show t.2 ∈ Icc (U t (1 / 4)) (U t (1 / 2)) from ⟨hlo.le, hhi.le⟩)
    have hl : (1 / 4 : ℝ) < r := by
      by_contra h
      have hh : r = 1 / 4 := le_antisymm (le_of_not_gt h) hr.1
      exact hlo.ne (hh ▸ heq)
    have hu : r < (1 / 2 : ℝ) := by
      by_contra h
      have hh : r = 1 / 2 := le_antisymm hr.2 (le_of_not_gt h)
      exact hhi.ne' (hh ▸ heq)
    exact ⟨r, ⟨hl, hu⟩, heq⟩
  have hOuter (t : ℝ × ℝ) (ht : t ∈ I) : ∃ r ∈ Ioo r0 r1, U t r = t.2 := by
    have he := hE t ht
    have hlo : t.2 < U t r0 := by
      have hh := he.2.2.2.2.1 r0 ⟨hr0.le, le_rfl⟩
      linarith only [hh, (hBounds t ht).1, (hBounds t ht).2.2.1]
    have hhi : U t r1 < t.2 := by linarith only [he.2.2.2.2.2.2.2, (hBounds t ht).2.2.2]
    obtain ⟨r, hr, heq⟩ := intermediate_value_Icc'
      hr01.le (hC t).continuousOn
      (show t.2 ∈ Icc (U t r1) (U t r0) from ⟨hhi.le, hlo.le⟩)
    have hl : r0 < r := by
      by_contra h
      have hh : r = r0 := le_antisymm (le_of_not_gt h) hr.1
      exact hlo.ne' (hh ▸ heq)
    have hu : r < r1 := by
      by_contra h
      have hh : r = r1 := le_antisymm hr.2 (le_of_not_gt h)
      exact hhi.ne (hh ▸ heq)
    exact ⟨r, ⟨hl, hu⟩, heq⟩
  let ri : ℝ × ℝ → ℝ := fun t => if ht : t ∈ I then Classical.choose (hInner t ht) else 0
  let ro : ℝ × ℝ → ℝ := fun t => if ht : t ∈ I then Classical.choose (hOuter t ht) else 0
  have hi (t : ℝ × ℝ) (ht : t ∈ I) : ri t ∈ Ioo (1 / 4 : ℝ) (1 / 2) ∧ U t (ri t) = t.2 := by
    simpa only [ri, dif_pos ht] using Classical.choose_spec (hInner t ht)
  have ho (t : ℝ × ℝ) (ht : t ∈ I) : ro t ∈ Ioo r0 r1 ∧ U t (ro t) = t.2 := by
    simpa only [ro, dif_pos ht] using Classical.choose_spec (hOuter t ht)
  have hdi (t : ℝ × ℝ) (ht : t ∈ I) : 17 / 320 < D t (ri t) :=
    (hE t ht).2.2.1 (ri t) ⟨(hi t ht).1.1.le, by linarith [(hi t ht).1.2]⟩
  have hdo (t : ℝ × ℝ) (ht : t ∈ I) : D t (ro t) < -93 / 64 :=
    (hE t ht).2.2.2.2.2.1 (ro t) ⟨(ho t ht).1.1.le, (ho t ht).1.2.trans hr1⟩
  have hiUnique (t : ℝ × ℝ) (ht : t ∈ I) (r : ℝ)
      (hr : r ∈ Ioo (1 / 4 : ℝ) (1 / 2)) (heq : U t r = t.2) : r = ri t :=
    (hE t ht).2.2.2.1.injOn
      ⟨hr.1.le, by linarith [hr.2]⟩
      ⟨(hi t ht).1.1.le, by linarith [(hi t ht).1.2]⟩
      (heq.trans (hi t ht).2.symm)
  have hoUnique (t : ℝ × ℝ) (ht : t ∈ I) (r : ℝ)
      (hr : r ∈ Ioo r0 r1) (heq : U t r = t.2) : r = ro t :=
    (hE t ht).2.2.2.2.2.2.1.injOn
      ⟨hr.1.le, (hr.2.trans hr1).le⟩
      ⟨(ho t ht).1.1.le, ((ho t ht).1.2.trans hr1).le⟩
      (heq.trans (ho t ht).2.symm)

  have hSmooth (a : ℝ × ℝ → ℝ) (lo hi : ℝ) (hlo : -1 ≤ lo) (hhi : hi ≤ 1)
      (ha : ∀ t ∈ I, a t ∈ Ioo lo hi ∧ U t (a t) = t.2 ∧ D t (a t) ≠ 0)
      (hunique : ∀ t ∈ I, ∀ r ∈ Ioo lo hi, U t r = t.2 → r = a t) :
      ContDiffOn ℝ ∞ a I := by
    intro t ht
    have hat := ha t ht
    have har : a t ∈ Ioo (-1 : ℝ) 1 :=
      ⟨hlo.trans_lt hat.1.1, hat.1.2.trans_le hhi⟩
    let F : (ℝ × ℝ) × ℝ → ℝ := fun p => U p.1 p.2 - p.1.2
    have hf : ContDiffAt ℝ ∞ F (t, a t) := hU.contDiffAt
      ((isOpen_univ.prod isOpen_Ioo).mem_nhds ⟨mem_univ _, har⟩)
    let L : ℝ →L[ℝ] ℝ := fderiv ℝ F (t, a t) ∘L ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ
    have hLone : L 1 = D t (a t) := by
      have hh := (hf.differentiableAt (by simp)).hasFDerivAt.comp (a t)
        (hasFDerivAt_prodMk_right (𝕜 := ℝ) t (a t))
      have hh' : HasDerivAt (fun r => U t r - t.2) (L 1) (a t) := hh.hasDerivAt
      exact hh'.unique ((hD t (a t) har).sub_const t.2)
    have hLapply (v : ℝ) : L v = D t (a t) * v := by
      calc
        L v = v * L 1 := by simpa using L.map_smul v (1 : ℝ)
        _ = D t (a t) * v := by rw [hLone, mul_comm]
    let Linv : ℝ →L[ℝ] ℝ := (D t (a t))⁻¹ • ContinuousLinearMap.id ℝ ℝ
    have hright : L ∘L Linv = ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      simp [Linv, hLapply, hat.2.2]
    have hleft : Linv ∘L L = ContinuousLinearMap.id ℝ ℝ := by
      apply ContinuousLinearMap.ext
      intro v
      simp [Linv, hLapply, hat.2.2]
    have hLI : L.IsInvertible := ContinuousLinearMap.IsInvertible.of_inverse hright hleft
    have hn : (∞ : ℕ∞ω) ≠ 0 := by simp
    let j : ℝ × ℝ → ℝ := hf.implicitFunction hn hLI
    have hj : ContDiffAt ℝ ∞ j t := hf.contDiffAt_implicitFunction hn hLI
    have hjt : j t = a t := hf.implicitFunction_apply_self hn hLI
    have hjbracket : ∀ᶠ x in 𝓝 t, j x ∈ Ioo lo hi :=
      hj.continuousAt.eventually (isOpen_Ioo.mem_nhds (hjt.symm ▸ hat.1))
    have heq : ∀ᶠ x in 𝓝 t, U x (j x) = x.2 := by
      have hh := hf.eventually_apply_implicitFunction hn hLI
      filter_upwards [hh] with x hx
      change U x (j x) - x.2 = U t (a t) - t.2 at hx
      rw [hat.2.1, sub_self] at hx
      exact sub_eq_zero.mp hx
    have hagree : a =ᶠ[𝓝 t] j := by
      filter_upwards [(isOpen_Ioo.prod isOpen_Ioo).mem_nhds ht, hjbracket, heq] with x hx hxb hxe
      exact (hunique x hx (j x) hxb hxe).symm
    exact (hj.congr_of_eventuallyEq hagree).contDiffWithinAt
  have his : ContDiffOn ℝ ∞ ri I := hSmooth ri (1 / 4) (1 / 2)
    (by norm_num) (by norm_num)
    (fun t ht => ⟨(hi t ht).1, (hi t ht).2, by linarith [hdi t ht]⟩) hiUnique
  have hos : ContDiffOn ℝ ∞ ro I := hSmooth ro r0 r1
    (by linarith only [hr0]) hr1.le
    (fun t ht => ⟨(ho t ht).1, (ho t ht).2, by linarith [hdo t ht]⟩) hoUnique
  have hHeightDerivative (a : ℝ × ℝ → ℝ)
      (hasmooth : ContDiffOn ℝ ∞ a I)
      (haroot : ∀ p ∈ I, U p (a p) = p.2)
      (habracket : ∀ p ∈ I, a p ∈ Ioo (-1 : ℝ) 1)
      (hanonzero : ∀ p ∈ I, D p (a p) ≠ 0)
      (p : ℝ × ℝ) (hp : p ∈ I) :
      HasDerivAt (fun h : ℝ => a (p.1, h)) (D p (a p))⁻¹ p.2 := by
    have harg : ContDiffAt ℝ ∞ (fun h : ℝ => (p.1, h)) p.2 :=
      contDiff_const.contDiffAt.prodMk contDiff_id.contDiffAt
    have hg : DifferentiableAt ℝ (fun h : ℝ => a (p.1, h)) p.2 :=
      ((hasmooth.contDiffAt ((isOpen_Ioo.prod isOpen_Ioo).mem_nhds hp)).comp p.2
        harg).differentiableAt (by simp)
    have hchain := (hD p (a p) (habracket p hp)).comp p.2 hg.hasDerivAt
    have heq : (fun h : ℝ => U p (a (p.1, h))) =ᶠ[𝓝 p.2] id := by
      filter_upwards [isOpen_Ioo.mem_nhds hp.2] with h hh
      exact haroot (p.1, h) ⟨hp.1, hh⟩
    have hprod : D p (a p) * deriv (fun h : ℝ => a (p.1, h)) p.2 = 1 :=
      (hchain.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id p.2)
    have hder : deriv (fun h : ℝ => a (p.1, h)) p.2 = (D p (a p))⁻¹ := by
      apply (mul_left_cancel₀ (hanonzero p hp))
      rw [hprod, mul_inv_cancel₀ (hanonzero p hp)]
    rw [← hder]
    exact hg.hasDerivAt
  have hid (p : ℝ × ℝ) (hp : p ∈ I) :
      HasDerivAt (fun h : ℝ => ri (p.1, h)) (D p (ri p))⁻¹ p.2 :=
    hHeightDerivative ri his (fun p hp => (hi p hp).2)
      (fun p hp => ⟨by linarith [(hi p hp).1.1], by linarith [(hi p hp).1.2]⟩)
      (fun p hp => by linarith [hdi p hp]) p hp
  have hod (p : ℝ × ℝ) (hp : p ∈ I) :
      HasDerivAt (fun h : ℝ => ro (p.1, h)) (D p (ro p))⁻¹ p.2 :=
    hHeightDerivative ro hos (fun p hp => (ho p hp).2)
      (fun p hp => ⟨by linarith [hr0, (ho p hp).1.1], (ho p hp).1.2.trans hr1⟩)
      (fun p hp => by linarith [hdo p hp]) p hp
  refine ⟨ri, ro, his, hos, ?_⟩
  intro t ht
  have hit := hi t ht
  have hot := ho t ht
  have he := hE t ht
  have hib : ri t ∈ Icc (1 / 4 : ℝ) (3 / 4) :=
    ⟨hit.1.1.le, by linarith only [hit.1.2]⟩
  have hob : ro t ∈ Icc r0 (1 : ℝ) := ⟨hot.1.1.le, (hot.1.2.trans hr1).le⟩
  have hbefore (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hri : r < ri t) : U t r < t.2 := by
    by_cases hl : r ≤ 1 / 4
    · have hh := he.1 r ⟨hr.1, hl⟩
      linarith only [hh, (hBounds t ht).1, (hBounds t ht).2.2.1]
    · have hh := he.2.2.2.1 ⟨(lt_of_not_ge hl).le, by linarith only [hri, hit.1.2]⟩
        hib hri
      exact hh.trans_eq hit.2
  have hafter (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1) (hor : ro t < r) : U t r < t.2 := by
    have hh := he.2.2.2.2.2.2.1 hob ⟨by linarith only [hot.1.1, hor], hr.2⟩ hor
    exact hh.trans_eq hot.2
  have hbetween (r : ℝ) (hr : r ∈ Icc (0 : ℝ) 1)
      (hir : ri t < r) (hro : r < ro t) : t.2 < U t r := by
    by_cases hm : r ≤ 3 / 4
    · have hh := he.2.2.2.1 hib ⟨by linarith only [hit.1.1, hir], hm⟩ hir
      exact hit.2.symm.trans_lt hh
    · by_cases ho : r ≤ r0
      · have hh := he.2.2.2.2.1 r ⟨(lt_of_not_ge hm).le, ho⟩
        linarith only [hh, (hBounds t ht).1, (hBounds t ht).2.2.1]
      · have hh := he.2.2.2.2.2.2.1 ⟨(lt_of_not_ge ho).le, hr.2⟩ hob hro
        exact hot.2.symm.trans_lt hh
  refine ⟨hit.1.1, hit.1.2, hot.1.1, hot.1.2, hit.2, hot.2, ?_,
    hdi t ht, hdo t ht, hid t ht, hod t ht⟩
  intro r hr
  have hequal : U t r = t.2 ↔ r = ri t ∨ r = ro t := by
    constructor
    · intro hu
      rcases lt_trichotomy r (ri t) with hb | heq | hi'
      · exact False.elim ((hbefore r hr hb).ne hu)
      · exact Or.inl heq
      · rcases lt_trichotomy r (ro t) with hb | heq | ho'
        · exact False.elim ((hbetween r hr hi' hb).ne' hu)
        · exact Or.inr heq
        · exact False.elim ((hafter r hr ho').ne hu)
    · rintro (rfl | rfl)
      · exact hit.2
      · exact hot.2
  have hless : U t r < t.2 ↔ r < ri t ∨ ro t < r := by
    constructor
    · intro hu
      by_cases hb : r < ri t
      · exact Or.inl hb
      · right
        by_contra h
        have hi' : ri t ≤ r := le_of_not_gt hb
        have ho' : r ≤ ro t := le_of_not_gt h
        rcases hi'.eq_or_lt with heq | hi'
        · exact hu.ne (by simpa only [← heq] using hit.2)
        · rcases ho'.eq_or_lt with heq | ho'
          · exact hu.ne (by simpa only [heq] using hot.2)
          · exact (hbetween r hr hi' ho').not_gt hu
    · rintro (hb | ha)
      · exact hbefore r hr hb
      · exact hafter r hr ha
  have hgreater : t.2 < U t r ↔ ri t < r ∧ r < ro t := by
    constructor
    · intro hu
      constructor
      · by_contra h
        rcases (le_of_not_gt h).eq_or_lt with heq | hb
        · exact hu.ne' (by simpa only [heq] using hit.2)
        · exact (hbefore r hr hb).not_gt hu
      · by_contra h
        rcases (le_of_not_gt h).eq_or_lt with heq | ha
        · exact hu.ne' (by simpa only [← heq] using hot.2)
        · exact (hafter r hr ha).not_gt hu
    · rintro ⟨hb, ha⟩
      exact hbetween r hr hb ha
  have hge : t.2 ≤ U t r ↔ ri t ≤ r ∧ r ≤ ro t := by
    rw [← not_lt, hless, not_or, not_lt, not_lt]
  exact ⟨hequal, hless, hgreater, hge⟩

end PoincareConjecture.M25.Topology3D.NestedReferenceLower
