
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
























open scoped Topology NNReal
open Set Metric


noncomputable section

namespace Poincare.ODE.Linear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]





theorem exists_hasDerivWithinAt_of_small {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℝ] E)
    (x₀ : E) {K : ℝ≥0} (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (hsmall : (b - a) * (K : ℝ) ≤ 1 / 2) :
    ∃ V : ℝ → E, V a = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt V (A t (V t)) (Icc a b) t := by
  set aBall : ℝ≥0 := 2 * (‖x₀‖₊ + 1) with haBall
  set L : ℝ≥0 := K * (‖x₀‖₊ + aBall) with hL
  have hPL : IsPicardLindelof (fun t x => A t x) (⟨a, by simp [hab]⟩ : Icc a b) x₀ aBall 0 L K := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro t ht
      exact ((A t).lipschitz.lipschitzOnWith).weaken (hK t ht)
    · intro x hx
      exact (hcont.clm_apply continuousOn_const)
    · intro t ht x hx
      rw [hL]
      push_cast
      calc ‖A t x‖ ≤ ‖A t‖ * ‖x‖ := (A t).le_opNorm x
        _ ≤ (K : ℝ) * ‖x‖ := by
              gcongr
              exact_mod_cast hK t ht
        _ ≤ (K : ℝ) * (‖x₀‖ + aBall) := by
              gcongr
              have : ‖x - x₀‖ ≤ (aBall : ℝ) := by rw [← dist_eq_norm]; exact hx
              calc ‖x‖ = ‖x - x₀ + x₀‖ := by rw [sub_add_cancel]
                _ ≤ ‖x - x₀‖ + ‖x₀‖ := norm_add_le _ _
                _ ≤ (aBall : ℝ) + ‖x₀‖ := by gcongr
                _ = ‖x₀‖ + aBall := by ring
        _ = (K : ℝ) * (‖x₀‖ + aBall) := by ring
    · have ht0 : (↑(⟨a, by simp [hab]⟩ : Icc a b) : ℝ) = a := rfl
      rw [ht0, sub_self, max_eq_left (by linarith : (0 : ℝ) ≤ b - a), hL, haBall]
      push_cast
      nlinarith [hsmall, norm_nonneg x₀, K.coe_nonneg, sub_nonneg.mpr hab,
        mul_nonneg (sub_nonneg.mpr hab) K.coe_nonneg]
  obtain ⟨V, hV0, hVd⟩ := hPL.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨V, hV0, hVd⟩

omit [CompleteSpace E] in




theorem exists_hasDerivWithinAt_glue {a c b : ℝ} (hac : a ≤ c) (hcb : c ≤ b)
    (A : ℝ → E →L[ℝ] E) {V₁ V₂ : ℝ → E}
    (h₁ : ∀ t ∈ Icc a c, HasDerivWithinAt V₁ (A t (V₁ t)) (Icc a c) t)
    (h₂ : ∀ t ∈ Icc c b, HasDerivWithinAt V₂ (A t (V₂ t)) (Icc c b) t)
    (hjoin : V₂ c = V₁ c) :
    ∃ V : ℝ → E, V a = V₁ a ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt V (A t (V t)) (Icc a b) t := by
  set V : ℝ → E := fun t => if t ≤ c then V₁ t else V₂ t with hV
  have hVval : ∀ x, V x = if x ≤ c then V₁ x else V₂ x := fun x => by rw [hV]
  have hVc : V c = V₁ c := by rw [hVval, if_pos le_rfl]
  refine ⟨V, by rw [hVval, if_pos hac], fun t ht => ?_⟩
  rcases lt_trichotomy t c with htc | htc | htc
  ·
    have hVt : V t = V₁ t := by rw [hVval, if_pos (le_of_lt htc)]
    have hset : (Icc a c : Set ℝ) =ᶠ[𝓝 t] Icc a b := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [isOpen_Iio.mem_nhds htc] with x hx
      simp only [Set.mem_Icc]
      exact ⟨fun h => ⟨h.1, h.2.trans hcb⟩, fun h => ⟨h.1, le_of_lt hx⟩⟩
    have hd := ((h₁ t ⟨ht.1, le_of_lt htc⟩).congr_set hset)
    have hVeq : V =ᶠ[𝓝[Icc a b] t] V₁ := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Iio.mem_nhds htc)] with x hx
      rw [hVval, if_pos (le_of_lt hx)]
    rw [hVt]
    exact hd.congr_of_eventuallyEq hVeq hVt
  ·
    subst htc
    have hleft : HasDerivWithinAt V (A t (V t)) (Icc a t) t := by
      have hd := h₁ t ⟨hac, le_rfl⟩
      rw [hVc]
      exact hd.congr (fun y hy => by rw [hVval, if_pos hy.2]) (by rw [hVval, if_pos le_rfl])
    have hright : HasDerivWithinAt V (A t (V t)) (Icc t b) t := by
      have hd := h₂ t ⟨le_rfl, hcb⟩
      rw [hVc, ← hjoin]
      refine hd.congr (fun y hy => ?_) (by rw [hVval, if_pos le_rfl, hjoin])
      rcases le_or_gt y t with hyt | hyt
      · rw [hVval, if_pos hyt, le_antisymm hyt hy.1, hjoin]
      · rw [hVval, if_neg (not_le.mpr hyt)]
    have hu := hleft.union hright
    rwa [Set.Icc_union_Icc_eq_Icc hac hcb] at hu
  ·
    have hVt : V t = V₂ t := by rw [hVval, if_neg (not_le.mpr htc)]
    have hset : (Icc c b : Set ℝ) =ᶠ[𝓝 t] Icc a b := by
      rw [Filter.eventuallyEq_set]
      filter_upwards [isOpen_Ioi.mem_nhds htc] with x hx
      simp only [Set.mem_Icc]
      exact ⟨fun h => ⟨hac.trans h.1, h.2⟩, fun h => ⟨le_of_lt hx, h.2⟩⟩
    have hd := ((h₂ t ⟨le_of_lt htc, ht.2⟩).congr_set hset)
    have hVeq : V =ᶠ[𝓝[Icc a b] t] V₂ := by
      filter_upwards [nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds htc)] with x hx
      rw [hVval, if_neg (not_le.mpr hx)]
    rw [hVt]
    exact hd.congr_of_eventuallyEq hVeq hVt









theorem exists_hasDerivWithinAt_Icc {a b : ℝ} (hab : a ≤ b) (A : ℝ → E →L[ℝ] E)
    (x₀ : E) {K : ℝ≥0} (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) :
    ∃ V : ℝ → E, V a = x₀ ∧
      ∀ t ∈ Icc a b, HasDerivWithinAt V (A t (V t)) (Icc a b) t := by
  have hba : (0 : ℝ) ≤ b - a := sub_nonneg.mpr hab
  set N : ℕ := ⌈2 * (b - a) * (K : ℝ)⌉₊ + 1 with hNdef
  have hN1 : 1 ≤ N := Nat.le_add_left 1 _
  have hNpos : (0 : ℝ) < N := by
    have : 0 < N := by omega
    exact_mod_cast this
  set s : ℕ → ℝ := fun i => a + (i : ℝ) * (b - a) / N with hs
  have hstep : (b - a) / N * (K : ℝ) ≤ 1 / 2 := by
    have hle : 2 * (b - a) * (K : ℝ) ≤ N := by
      rw [hNdef]; push_cast; linarith [Nat.le_ceil (2 * (b - a) * (K : ℝ))]
    rw [div_mul_eq_mul_div, div_le_iff₀ hNpos]
    nlinarith [hle]
  have hsN : s N = b := by
    simp only [hs]; field_simp; ring
  have ha_le_s : ∀ i, a ≤ s i := fun i => by
    simp only [hs]
    have : (0 : ℝ) ≤ (i : ℝ) * (b - a) / N :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg i) hba) hNpos.le
    linarith
  have hs_mono : ∀ i, s i ≤ s (i + 1) := fun i => by
    have hd : s (i + 1) - s i = (b - a) / N := by simp only [hs]; push_cast; ring
    have : (0 : ℝ) ≤ (b - a) / N := div_nonneg hba hNpos.le
    linarith [hd, this]
  have hs_le_b : ∀ i, i ≤ N → s i ≤ b := fun i hi => by
    simp only [hs]
    have key : (i : ℝ) * (b - a) / N ≤ b - a := by
      rw [div_le_iff₀ hNpos]
      calc (i : ℝ) * (b - a) ≤ (N : ℝ) * (b - a) :=
            mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hba
        _ = (b - a) * N := by ring
    linarith
  have hsmall_step : ∀ i, (s (i + 1) - s i) * (K : ℝ) ≤ 1 / 2 := fun i => by
    have hd : s (i + 1) - s i = (b - a) / N := by simp only [hs]; push_cast; ring
    rw [hd]; exact hstep
  have aux : ∀ i, i ≤ N → ∃ V : ℝ → E, V a = x₀ ∧
      ∀ t ∈ Icc a (s i), HasDerivWithinAt V (A t (V t)) (Icc a (s i)) t := by
    intro i
    induction i with
    | zero =>
      intro _
      have hs0 : s 0 = a := by simp [hs]
      obtain ⟨V, hV0, hVd⟩ := exists_hasDerivWithinAt_of_small (le_of_eq hs0.symm) A x₀
        (hcont.mono (by rw [hs0]; exact Icc_subset_Icc le_rfl hab))
        (fun t ht => hK t (by rw [hs0] at ht; exact ⟨ht.1, ht.2.trans hab⟩))
        (by rw [hs0, sub_self, zero_mul]; norm_num)
      exact ⟨V, hV0, hVd⟩
    | succ n ih =>
      intro hn
      obtain ⟨V₁, hV₁0, hV₁d⟩ := ih (Nat.le_of_succ_le hn)
      have hsub : Icc (s n) (s (n + 1)) ⊆ Icc a b :=
        Icc_subset_Icc (ha_le_s n) (hs_le_b (n + 1) hn)
      obtain ⟨V₂, hV₂0, hV₂d⟩ := exists_hasDerivWithinAt_of_small (hs_mono n) A (V₁ (s n))
        (hcont.mono hsub) (fun t ht => hK t (hsub ht)) (hsmall_step n)
      obtain ⟨V, hVa, hVd⟩ := exists_hasDerivWithinAt_glue (ha_le_s n) (hs_mono n) A
        hV₁d hV₂d hV₂0
      exact ⟨V, hVa.trans hV₁0, hVd⟩
  obtain ⟨V, hV0, hVd⟩ := aux N le_rfl
  rw [hsN] at hVd
  exact ⟨V, hV0, hVd⟩









def IsSolOn (A : ℝ → E →L[ℝ] E) (a b : ℝ) (V : ℝ → E) : Prop :=
  ∀ t ∈ Icc a b, HasDerivWithinAt V (A t (V t)) (Icc a b) t

omit [CompleteSpace E] in
theorem IsSolOn.continuousOn {A : ℝ → E →L[ℝ] E} {a b : ℝ} {V : ℝ → E}
    (h : IsSolOn A a b V) : ContinuousOn V (Icc a b) :=
  fun t ht => (h t ht).continuousWithinAt




theorem Icc_mem_nhdsWithin_Ici {a b t : ℝ} (ht : t ∈ Ico a b) : Icc a b ∈ 𝓝[≥] t := by
  refine mem_nhdsWithin.mpr ⟨Iio b, isOpen_Iio, ht.2, ?_⟩
  rintro x ⟨hxb, hxt⟩
  exact ⟨le_trans ht.1 hxt, le_of_lt hxb⟩



theorem Icc_mem_nhdsWithin_Iic {a b t : ℝ} (ht : t ∈ Ioc a b) : Icc a b ∈ 𝓝[≤] t := by
  refine mem_nhdsWithin.mpr ⟨Ioi a, isOpen_Ioi, ht.1, ?_⟩
  rintro x ⟨hxa, hxt⟩
  exact ⟨le_of_lt hxa, le_trans hxt ht.2⟩

omit [CompleteSpace E] in




theorem IsSolOn.eqOn_of_left {A : ℝ → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) {V W : ℝ → E}
    (hV : IsSolOn A a b V) (hW : IsSolOn A a b W) (ha : V a = W a) :
    EqOn V W (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_right
    (v := fun t x => A t x) (s := fun _ => univ)
    (fun t ht => ((A t).lipschitz.lipschitzOnWith).weaken (hK t ⟨ht.1, ht.2.le⟩))
    hV.continuousOn
    (fun t ht => (hV t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Ici ht))
    (fun _ _ => mem_univ _)
    hW.continuousOn
    (fun t ht => (hW t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Ici ht))
    (fun _ _ => mem_univ _) ha

omit [CompleteSpace E] in



theorem IsSolOn.eqOn_of_right {A : ℝ → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) {V W : ℝ → E}
    (hV : IsSolOn A a b V) (hW : IsSolOn A a b W) (hb : V b = W b) :
    EqOn V W (Icc a b) :=
  ODE_solution_unique_of_mem_Icc_left
    (v := fun t x => A t x) (s := fun _ => univ)
    (fun t ht => ((A t).lipschitz.lipschitzOnWith).weaken (hK t ⟨ht.1.le, ht.2⟩))
    hV.continuousOn
    (fun t ht => (hV t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Iic ht))
    (fun _ _ => mem_univ _)
    hW.continuousOn
    (fun t ht => (hW t ⟨ht.1.le, ht.2⟩).mono_of_mem_nhdsWithin (Icc_mem_nhdsWithin_Iic ht))
    (fun _ _ => mem_univ _) hb

omit [CompleteSpace E] in


theorem IsSolOn.add {A : ℝ → E →L[ℝ] E} {a b : ℝ} {V W : ℝ → E}
    (hV : IsSolOn A a b V) (hW : IsSolOn A a b W) : IsSolOn A a b (V + W) := by
  intro t ht
  have h := (hV t ht).add (hW t ht)
  simpa only [Pi.add_apply, map_add] using h

omit [CompleteSpace E] in

theorem IsSolOn.const_smul {A : ℝ → E →L[ℝ] E} {a b : ℝ} (c : ℝ) {V : ℝ → E}
    (hV : IsSolOn A a b V) : IsSolOn A a b (c • V) := by
  intro t ht
  have h := (hV t ht).const_smul c
  simpa only [Pi.smul_apply, ContinuousLinearMap.map_smul] using h

variable {A : ℝ → E →L[ℝ] E} {a b : ℝ} {K : ℝ≥0}



noncomputable def solOf (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (x₀ : E) : ℝ → E :=
  Classical.choose (exists_hasDerivWithinAt_Icc hab A x₀ hcont hK)

theorem solOf_left (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (x₀ : E) : solOf hab hcont hK x₀ a = x₀ :=
  (Classical.choose_spec (exists_hasDerivWithinAt_Icc hab A x₀ hcont hK)).1

theorem solOf_isSolOn (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (x₀ : E) : IsSolOn A a b (solOf hab hcont hK x₀) :=
  (Classical.choose_spec (exists_hasDerivWithinAt_Icc hab A x₀ hcont hK)).2

theorem solOf_add (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (x y : E) {t : ℝ} (ht : t ∈ Icc a b) :
    solOf hab hcont hK (x + y) t = solOf hab hcont hK x t + solOf hab hcont hK y t := by
  have hinit : solOf hab hcont hK (x + y) a =
      (solOf hab hcont hK x + solOf hab hcont hK y) a := by
    simp [solOf_left]
  have heq := IsSolOn.eqOn_of_left hK (solOf_isSolOn hab hcont hK (x + y))
    ((solOf_isSolOn hab hcont hK x).add (solOf_isSolOn hab hcont hK y)) hinit ht
  simpa only [Pi.add_apply] using heq

theorem solOf_smul (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (c : ℝ) (x : E) {t : ℝ} (ht : t ∈ Icc a b) :
    solOf hab hcont hK (c • x) t = c • solOf hab hcont hK x t := by
  have hinit : solOf hab hcont hK (c • x) a =
      (c • solOf hab hcont hK x) a := by
    simp [solOf_left]
  have heq := IsSolOn.eqOn_of_left hK (solOf_isSolOn hab hcont hK (c • x))
    ((solOf_isSolOn hab hcont hK x).const_smul c) hinit ht
  simpa only [Pi.smul_apply] using heq




noncomputable def flowMap (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) : E →ₗ[ℝ] E where
  toFun x₀ := solOf hab hcont hK x₀ b
  map_add' x y := by
    have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have hleft : solOf hab hcont hK (x + y) a
        = (solOf hab hcont hK x + solOf hab hcont hK y) a := by
      simp only [Pi.add_apply, solOf_left]
    have heq := IsSolOn.eqOn_of_left hK (solOf_isSolOn hab hcont hK (x + y))
      ((solOf_isSolOn hab hcont hK x).add (solOf_isSolOn hab hcont hK y)) hleft hb
    simpa only [Pi.add_apply] using heq
  map_smul' c x := by
    have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
    have hleft : solOf hab hcont hK (c • x) a = (c • solOf hab hcont hK x) a := by
      simp only [Pi.smul_apply, solOf_left]
    have heq := IsSolOn.eqOn_of_left hK (solOf_isSolOn hab hcont hK (c • x))
      ((solOf_isSolOn hab hcont hK x).const_smul c) hleft hb
    simpa only [RingHom.id_apply, Pi.smul_apply] using heq

@[simp] theorem flowMap_apply (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) (x₀ : E) :
    flowMap hab hcont hK x₀ = solOf hab hcont hK x₀ b := rfl




theorem flowMap_injective (hab : a ≤ b) (hcont : ContinuousOn A (Icc a b))
    (hK : ∀ t ∈ Icc a b, ‖A t‖₊ ≤ K) : Function.Injective (flowMap hab hcont hK) := by
  intro x y hxy
  have hb : solOf hab hcont hK x b = solOf hab hcont hK y b := by
    simpa only [flowMap_apply] using hxy
  have heq := IsSolOn.eqOn_of_right hK (solOf_isSolOn hab hcont hK x)
    (solOf_isSolOn hab hcont hK y) hb
  have ha := heq (show a ∈ Icc a b from ⟨le_rfl, hab⟩)
  rwa [solOf_left, solOf_left] at ha

end Poincare.ODE.Linear
