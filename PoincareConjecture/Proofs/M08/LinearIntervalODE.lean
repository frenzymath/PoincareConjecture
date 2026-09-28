import Mathlib.Analysis.ODE.ExistUnique

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology NNReal ContDiff

universe uODE

namespace PoincareConjecture.M08

variable {E : Type uODE} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem linearODE_piecewise_Icc (L : ℝ → E →L[ℝ] E) {a c b : ℝ}
    (hac : a ≤ c) (hcb : c ≤ b) {f g : ℝ → E}
    (hf : ∀ s ∈ Icc a c, HasDerivWithinAt f (L s (f s)) (Icc a c) s)
    (hg : ∀ s ∈ Icc c b, HasDerivWithinAt g (L s (g s)) (Icc c b) s)
    (hfg : f c = g c) :
    ∀ s ∈ Icc a b, HasDerivWithinAt ((Iic c).piecewise f g)
      (L s ((Iic c).piecewise f g s)) (Icc a b) s := by
  classical
  let z := (Iic c).piecewise f g
  have hleft (s : ℝ) (hs : s ≤ c) : z s = f s :=
    piecewise_eq_of_mem (Iic c) f g hs
  have hright (s : ℝ) (hs : c ≤ s) : z s = g s := by
    by_cases hsc : s ≤ c
    · have hsc' : s = c := le_antisymm hsc hs
      rw [hsc', hleft c le_rfl, hfg]
    · exact piecewise_eq_of_notMem (Iic c) f g hsc
  have hdleft (s : ℝ) (hs : s ∈ Icc a c) :
      HasDerivWithinAt z (L s (z s)) (Icc a c) s := by
    rw [hleft s hs.2]
    exact (hf s hs).congr_of_mem (fun r hr ↦ hleft r hr.2) hs
  have hdright (s : ℝ) (hs : s ∈ Icc c b) :
      HasDerivWithinAt z (L s (z s)) (Icc c b) s := by
    rw [hright s hs.1]
    exact (hg s hs).congr_of_mem (fun r hr ↦ hright r hr.1) hs
  intro s hs
  change HasDerivWithinAt z (L s (z s)) (Icc a b) s
  rcases lt_trichotomy s c with hsc | rfl | hcs
  · apply (hdleft s ⟨hs.1, hsc.le⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hsc)]
      with r hr hrc
    exact ⟨hr.1, hrc.le⟩
  · simpa only [Icc_union_Icc_eq_Icc hac hcb] using
      (hdleft s ⟨hac, le_rfl⟩).union (hdright s ⟨le_rfl, hcb⟩)
  · apply (hdright s ⟨hcs.le, hs.2⟩).mono_of_mem_nhdsWithin
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds hcs)]
      with r hr hcr
    exact ⟨hcr.le, hr.2⟩

theorem linear_interval_solution_unique (L : ℝ → E →L[ℝ] E) {a b t₀ : ℝ}
    (hL : ContinuousOn L (Icc a b)) (ht₀ : t₀ ∈ Icc a b) {f g : ℝ → E}
    (hf : ∀ s ∈ Icc a b, HasDerivWithinAt f (L s (f s)) (Icc a b) s)
    (hg : ∀ s ∈ Icc a b, HasDerivWithinAt g (L s (g s)) (Icc a b) s)
    (heq : f t₀ = g t₀) : EqOn f g (Icc a b) := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hL
  let K : ℝ≥0 := ⟨max C 0, le_max_right _ _⟩
  have hlip (s : ℝ) (hs : s ∈ Icc a b) : LipschitzOnWith K (L s) (univ : Set E) :=
    ((L s).lipschitzWith_of_opNorm_le ((hC s hs).trans (le_max_left _ _))).lipschitzOnWith
  have hfc : ContinuousOn f (Icc a b) := HasDerivWithinAt.continuousOn hf
  have hgc : ContinuousOn g (Icc a b) := HasDerivWithinAt.continuousOn hg
  have hleft : EqOn f g (Icc a t₀) := by
    apply ODE_solution_unique_of_mem_Icc_left (s := fun _ ↦ univ) (K := K)
      (fun s hs ↦ hlip s ⟨hs.1.le, hs.2.trans ht₀.2⟩)
      (hfc.mono (Icc_subset_Icc_right ht₀.2))
      (fun s hs ↦ (hf s ⟨hs.1.le, hs.2.trans ht₀.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩))
      (fun _ _ ↦ mem_univ _) (hgc.mono (Icc_subset_Icc_right ht₀.2))
      (fun s hs ↦ (hg s ⟨hs.1.le, hs.2.trans ht₀.2⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE_of_mem ⟨hs.1, hs.2.trans ht₀.2⟩))
      (fun _ _ ↦ mem_univ _) heq
  have hright : EqOn f g (Icc t₀ b) := by
    apply ODE_solution_unique_of_mem_Icc_right (s := fun _ ↦ univ) (K := K)
      (fun s hs ↦ hlip s ⟨ht₀.1.trans hs.1, hs.2.le⟩)
      (hfc.mono (Icc_subset_Icc_left ht₀.1))
      (fun s hs ↦ (hf s ⟨ht₀.1.trans hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩))
      (fun _ _ ↦ mem_univ _) (hgc.mono (Icc_subset_Icc_left ht₀.1))
      (fun s hs ↦ (hg s ⟨ht₀.1.trans hs.1, hs.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGE_of_mem ⟨ht₀.1.trans hs.1, hs.2⟩))
      (fun _ _ ↦ mem_univ _) heq
  intro s hs
  rcases le_total s t₀ with h | h
  · exact hleft ⟨hs.1, h⟩
  · exact hright ⟨h, hs.2⟩

variable [CompleteSpace E]

theorem exists_linear_interval_solution_short (L : ℝ → E →L[ℝ] E)
    {a b t₀ K δ : ℝ} (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hstep : 2 * K * δ ≤ 1)
    (hL : ContinuousOn L (Icc a b)) (ht₀ : t₀ ∈ Icc a b)
    (hbound : ∀ s ∈ Icc a b, ‖L s‖ ≤ K)
    (hlen : max (b - t₀) (t₀ - a) ≤ δ) (z₀ : E) :
    ∃ z : ℝ → E, z t₀ = z₀ ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt z (L s (z s)) (Icc a b) s := by
  let A := ‖z₀‖ + 1
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let Ar : ℝ≥0 := ⟨A, hA⟩
  let B : ℝ≥0 := ⟨2 * K * A, by positivity⟩
  let Kr : ℝ≥0 := ⟨K, hK⟩
  have hpl : IsPicardLindelof (fun s z ↦ L s z) ⟨t₀, ht₀⟩ z₀ Ar 0 B Kr := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro s hs
      exact ((L s).lipschitzWith_of_opNorm_le (K := Kr) (hbound s hs)).lipschitzOnWith
    · intro z _
      exact hL.clm_apply continuousOn_const
    · intro s hs z hz
      have hdist : ‖z - z₀‖ ≤ A := by
        change dist z z₀ ≤ A at hz
        rwa [dist_eq_norm] at hz
      have hzbound : ‖z‖ ≤ 2 * A := by
        have := norm_le_norm_sub_add z z₀
        dsimp only [A] at *
        linarith
      change ‖L s z‖ ≤ 2 * K * A
      calc
        ‖L s z‖ ≤ ‖L s‖ * ‖z‖ := (L s).le_opNorm z
        _ ≤ K * (2 * A) := mul_le_mul (hbound s hs) hzbound (norm_nonneg _) hK
        _ = 2 * K * A := by ring
    · change (2 * K * A) * max (b - t₀) (t₀ - a) ≤ A - 0
      rw [sub_zero]
      calc
        (2 * K * A) * max (b - t₀) (t₀ - a) ≤ (2 * K * A) * δ :=
          mul_le_mul_of_nonneg_left hlen (by positivity)
        _ = A * (2 * K * δ) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hstep hA
        _ = A := mul_one A
  exact hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

theorem exists_linear_interval_solution_left_bounded (L : ℝ → E →L[ℝ] E)
    (K δ : ℝ) (hK : 0 ≤ K) (hδ : 0 < δ) (hstep : 2 * K * δ ≤ 1) :
    ∀ (N : ℕ) {a b : ℝ}, a ≤ b → b - a ≤ (N : ℝ) * δ →
      ContinuousOn L (Icc a b) → (∀ s ∈ Icc a b, ‖L s‖ ≤ K) →
      ∀ z₀ : E, ∃ z : ℝ → E, z a = z₀ ∧
        ∀ s ∈ Icc a b, HasDerivWithinAt z (L s (z s)) (Icc a b) s := by
  intro N
  induction N with
  | zero =>
    intro a b hab hlen hL hbound z₀
    apply exists_linear_interval_solution_short L hK hδ.le hstep hL
      ⟨le_rfl, hab⟩ hbound ?_ z₀
    rw [sub_self, max_eq_left (sub_nonneg.mpr hab)]
    simp only [Nat.cast_zero, zero_mul] at hlen
    exact hlen.trans hδ.le
  | succ N ih =>
    intro a b hab hlen hL hbound z₀
    let c := min b (a + δ)
    have hac : a ≤ c := le_min hab (le_add_of_nonneg_right hδ.le)
    have hcb : c ≤ b := min_le_left _ _
    have hclen : c - a ≤ δ := by
      have h := min_le_right b (a + δ)
      change c ≤ a + δ at h
      linarith
    have hsubleft : Icc a c ⊆ Icc a b := Icc_subset_Icc_right hcb
    obtain ⟨f, hfa, hfd⟩ := exists_linear_interval_solution_short L hK hδ.le hstep
      (hL.mono hsubleft) ⟨le_rfl, hac⟩ (fun s hs ↦ hbound s (hsubleft hs))
      (by simpa only [sub_self, max_eq_left (sub_nonneg.mpr hac)] using hclen) z₀
    have hremain : b - c ≤ (N : ℝ) * δ := by
      by_cases hb : b ≤ a + δ
      · rw [show c = b from min_eq_left hb, sub_self]
        exact mul_nonneg (Nat.cast_nonneg _) hδ.le
      · rw [show c = a + δ from min_eq_right (le_of_not_ge hb)]
        simp only [Nat.cast_succ, add_mul, one_mul] at hlen
        linarith
    have hsubright : Icc c b ⊆ Icc a b := Icc_subset_Icc_left hac
    obtain ⟨g, hgc, hgd⟩ := ih hcb hremain (hL.mono hsubright)
      (fun s hs ↦ hbound s (hsubright hs)) (f c)
    refine ⟨(Iic c).piecewise f g, ?_, linearODE_piecewise_Icc L hac hcb hfd hgd hgc.symm⟩
    rw [piecewise_eq_of_mem (Iic c) f g hac]
    exact hfa

theorem exists_linear_interval_solution_left (L : ℝ → E →L[ℝ] E)
    {a b : ℝ} (hab : a ≤ b) (hL : ContinuousOn L (Icc a b)) (z₀ : E) :
    ∃ z : ℝ → E, z a = z₀ ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt z (L s (z s)) (Icc a b) s := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hL
  let K := max C 0
  have hK : 0 ≤ K := le_max_right _ _
  let δ := 1 / (2 * (K + 1))
  have hden : 0 < 2 * (K + 1) := by positivity
  have hδ : 0 < δ := one_div_pos.mpr hden
  have hstep : 2 * K * δ ≤ 1 := by
    dsimp only [δ]
    rw [mul_one_div]
    apply (div_le_iff₀ hden).mpr
    linarith
  obtain ⟨N, hN⟩ := exists_nat_ge ((b - a) / δ)
  exact exists_linear_interval_solution_left_bounded L K δ hK hδ hstep N hab
    ((div_le_iff₀ hδ).mp hN) hL (fun s hs ↦ (hC s hs).trans (le_max_left _ _)) z₀

theorem exists_linear_interval_solution (L : ℝ → E →L[ℝ] E)
    {a b t₀ : ℝ} (hL : ContinuousOn L (Icc a b)) (ht₀ : t₀ ∈ Icc a b) (z₀ : E) :
    ∃ z : ℝ → E, z t₀ = z₀ ∧
      ∀ s ∈ Icc a b, HasDerivWithinAt z (L s (z s)) (Icc a b) s := by
  obtain ⟨f, hf₀, hfd⟩ := exists_linear_interval_solution_left L ht₀.2
    (hL.mono (Icc_subset_Icc_left ht₀.1)) z₀
  let Lrev : ℝ → E →L[ℝ] E := fun s ↦ -L (-s)
  have hrevmap : MapsTo Neg.neg (Icc (-t₀) (-a)) (Icc a t₀) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hLrev : ContinuousOn Lrev (Icc (-t₀) (-a)) :=
    ((hL.mono (Icc_subset_Icc_right ht₀.2)).comp continuous_neg.continuousOn hrevmap).neg
  obtain ⟨q, hq₀, hqd⟩ := exists_linear_interval_solution_left Lrev
    (neg_le_neg ht₀.1) hLrev z₀
  let g := q ∘ Neg.neg
  have hg₀ : g t₀ = z₀ := hq₀
  have hback : MapsTo Neg.neg (Icc a t₀) (Icc (-t₀) (-a)) := by
    intro s hs
    constructor <;> linarith [hs.1, hs.2]
  have hgd (s : ℝ) (hs : s ∈ Icc a t₀) :
      HasDerivWithinAt g (L s (g s)) (Icc a t₀) s := by
    have h := (hqd (-s) (hback hs)).scomp s (hasDerivAt_neg s).hasDerivWithinAt hback
    simpa [g, Lrev] using h
  refine ⟨(Iic t₀).piecewise g f, ?_,
    linearODE_piecewise_Icc L ht₀.1 ht₀.2 hgd hfd (hg₀.trans hf₀.symm)⟩
  rw [piecewise_eq_of_mem (Iic t₀) g f (show t₀ ∈ Iic t₀ from le_refl t₀)]
  exact hg₀

theorem linear_interval_solution_contDiffOn (L : ℝ → E →L[ℝ] E) {a b : ℝ}
    (hL : ContDiffOn ℝ ∞ L (Icc a b)) {z : ℝ → E}
    (hz : ∀ s ∈ Icc a b, HasDerivWithinAt z (L s (z s)) (Icc a b) s) :
    ContDiffOn ℝ ∞ z (Icc a b) := by
  have hfield : ContDiffOn ℝ ∞ (fun p : ℝ × E ↦ L p.1 p.2) (Icc a b ×ˢ univ) :=
    (hL.comp contDiffOn_fst (fun p hp ↦ hp.1)).clm_apply contDiffOn_snd
  exact ODE.contDiffOn_enat_Icc_of_hasDerivWithinAt (n := ⊤)
    (f := fun s z ↦ L s z) (u := univ) hfield hz
    (fun _ _ ↦ mem_univ _)

end PoincareConjecture.M08
