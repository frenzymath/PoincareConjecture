import PoincareConjecture.Proofs.M63.Mathlib.PeriodicSmoothApproximation

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace PoincareConjecture.M63

theorem exists_periodic_C2_relabeling_tolerance
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 < L) {c : ℝ → E} (hc : ContDiff ℝ 2 c)
    (hp : Function.Periodic c L) {eps : ℝ} (heps : 0 < eps) :
    ∃ δ > 0, ∀ r : ℝ → E, ContDiff ℝ 2 r → Function.Periodic r L →
      ∀ ψ : ℝ → ℝ, ContDiff ℝ 2 ψ → (∀ x, ψ (x + L) = ψ x + L) →
      (∀ x, ‖r x - c x‖ < δ ∧ ‖deriv r x - deriv c x‖ < δ ∧
        ‖deriv (deriv r) x - deriv (deriv c) x‖ < δ) →
      (∀ x, |ψ x - x| < δ ∧ |deriv ψ x - 1| < δ ∧
        |deriv (deriv ψ) x| < δ) →
      ContDiff ℝ 2 (fun x => r (ψ x)) ∧ Function.Periodic (fun x => r (ψ x)) L ∧
      ∀ x, ‖r (ψ x) - c x‖ < eps ∧
        ‖deriv (fun y => r (ψ y)) x - deriv c x‖ < eps ∧
        ‖deriv (deriv (fun y => r (ψ y))) x - deriv (deriv c) x‖ < eps := by
  let : Fact (0 < L) := ⟨hL⟩
  have hc1 : ContDiff ℝ 1 (deriv c) := hc.deriv' (n := 1)
  have hp1 := hp.deriv_of_differentiable (hc.differentiable (by norm_num))
  have hp2 := hp1.deriv_of_differentiable (hc1.differentiable (by norm_num))
  let J := fun x => (c x, deriv c x, deriv (deriv c) x)
  have hJper : Function.Periodic J L := by
    intro x
    dsimp only [J]
    rw [hp x, hp1 x, hp2 x]
  let f : C(AddCircle L, E × E × E) := ⟨hJper.lift,
    (QuotientAddGroup.isQuotientMap_mk (AddSubgroup.zmultiples L)).continuous_iff.mpr
      (hc.continuous.prodMk (hc1.continuous.prodMk hc1.continuous_deriv_one))⟩
  have hf (x : ℝ) : f (x : AddCircle L) = J x := rfl
  let C := 1 + ‖f‖
  have hC : 1 ≤ C := by dsimp [C]; linarith [norm_nonneg f]
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hcb1 (x : ℝ) : ‖deriv c x‖ ≤ C := by
    have h := (norm_fst_le (f (x : AddCircle L)).2).trans
      ((norm_snd_le _).trans (f.norm_coe_le_norm (x : AddCircle L)))
    exact h.trans (by dsimp [C]; linarith)
  have hcb2 (x : ℝ) : ‖deriv (deriv c) x‖ ≤ C := by
    have h := (norm_snd_le (f (x : AddCircle L)).2).trans
      ((norm_snd_le _).trans (f.norm_coe_le_norm (x : AddCircle L)))
    exact h.trans (by dsimp [C]; linarith)
  let η := eps / (16 * (C + 1))
  have hden : 0 < 16 * (C + 1) := by positivity
  have hη : 0 < η := div_pos heps hden
  have hηeq : η * (16 * (C + 1)) = eps := div_mul_cancel₀ _ hden.ne'
  have hnorm : Continuous (fun s : ℝ => ‖periodicTranslation s f - f‖) :=
    ((continuous_periodicTranslation.comp
      (continuous_id.prodMk continuous_const)).sub continuous_const).norm
  have hzero : ‖periodicTranslation 0 f - f‖ < η := by
    have hsame : periodicTranslation 0 f = f := by
      apply ContinuousMap.ext
      intro x
      change f (x - (0 : AddCircle L)) = f x
      rw [sub_zero]
    simpa only [hsame, sub_self, norm_zero] using hη
  obtain ⟨ρ, hρ, hnear⟩ := Metric.mem_nhds_iff.mp
    (hnorm.continuousAt.eventually (isOpen_Iio.mem_nhds hzero))
  have hmod (s : ℝ) (hs : |s| < ρ) (x : ℝ) : ‖J (x - s) - J x‖ < η := by
    have hn : ‖periodicTranslation s f - f‖ < η :=
      hnear (by simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hs)
    have h := ((periodicTranslation s f - f).norm_coe_le_norm
      (x : AddCircle L)).trans_lt hn
    change ‖f ((x : AddCircle L) - (s : AddCircle L)) - f (x : AddCircle L)‖ < η at h
    simpa only [← AddCircle.coe_sub, hf] using h
  let δ := min (1 / 2) (min η (ρ / 2))
  have hδ : 0 < δ := lt_min (by norm_num) (lt_min hη (half_pos hρ))
  have hδ1 : δ ≤ 1 := (min_le_left _ _).trans (by norm_num)
  have hδη : δ ≤ η := (min_le_right _ _).trans (min_le_left _ _)
  have hδρ : δ < ρ :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hρ)
  refine ⟨δ, hδ, ?_⟩
  intro r hr hrp ψ hψ hψp happ hlabel
  have hr1 : ContDiff ℝ 1 (deriv r) := hr.deriv' (n := 1)
  have hψ1 : ContDiff ℝ 1 (deriv ψ) := hψ.deriv' (n := 1)
  have hqd (x : ℝ) : HasDerivAt (fun y => r (ψ y))
      (deriv ψ x • deriv r (ψ x)) x :=
    (hr.differentiable (by norm_num) (ψ x)).hasDerivAt.scomp x
      (hψ.differentiable (by norm_num) x).hasDerivAt
  have hqd_eq : deriv (fun y => r (ψ y)) = fun x => deriv ψ x • deriv r (ψ x) :=
    funext fun x => (hqd x).deriv
  have hqdd (x : ℝ) : deriv (deriv (fun y => r (ψ y))) x =
      (deriv ψ x) ^ 2 • deriv (deriv r) (ψ x) +
        deriv (deriv ψ) x • deriv r (ψ x) := by
    rw [hqd_eq]
    have hd := ((hψ1.differentiable (by norm_num) x).hasDerivAt).smul
      ((hr1.differentiable (by norm_num) (ψ x)).hasDerivAt.scomp x
        (hψ.differentiable (by norm_num) x).hasDerivAt)
    change HasDerivAt (fun y => deriv ψ y • deriv r (ψ y))
      (deriv ψ x • (deriv ψ x • deriv (deriv r) (ψ x)) +
        deriv (deriv ψ) x • deriv r (ψ x)) x at hd
    simpa only [← mul_smul, ← pow_two] using hd.deriv
  refine ⟨hr.comp hψ, ?_, ?_⟩
  · intro x
    change r (ψ (x + L)) = r (ψ x)
    rw [hψp x, hrp (ψ x)]
  intro x
  have hshift := hmod (x - ψ x)
    (by simpa only [abs_sub_comm] using (hlabel x).1.trans hδρ) x
  rw [sub_sub_cancel] at hshift
  have hshift0 : ‖c (ψ x) - c x‖ < η := (norm_fst_le _).trans_lt hshift
  have hshift1 : ‖deriv c (ψ x) - deriv c x‖ < η :=
    ((norm_fst_le _).trans (norm_snd_le _)).trans_lt hshift
  have hshift2 : ‖deriv (deriv c) (ψ x) - deriv (deriv c) x‖ < η :=
    ((norm_snd_le _).trans (norm_snd_le _)).trans_lt hshift
  have herr0 : ‖r (ψ x) - c x‖ < 2 * η := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (r (ψ x)) (c (ψ x)) (c x)).trans_lt
      (add_lt_add ((happ (ψ x)).1.trans_le hδη) hshift0)
    linarith only [h]
  have herr1 : ‖deriv r (ψ x) - deriv c x‖ < 2 * η := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (deriv r (ψ x)) (deriv c (ψ x))
      (deriv c x)).trans_lt (add_lt_add ((happ (ψ x)).2.1.trans_le hδη) hshift1)
    linarith only [h]
  have herr2 : ‖deriv (deriv r) (ψ x) - deriv (deriv c) x‖ < 2 * η := by
    have h := (norm_sub_le_norm_sub_add_norm_sub (deriv (deriv r) (ψ x))
      (deriv (deriv c) (ψ x)) (deriv (deriv c) x)).trans_lt
        (add_lt_add ((happ (ψ x)).2.2.trans_le hδη) hshift2)
    linarith only [h]
  let a := deriv ψ x
  let b := deriv (deriv ψ) x
  have ha1 : |a - 1| ≤ δ := (hlabel x).2.1.le
  have ha : |a| ≤ 2 := by
    rcases abs_le.mp ha1 with ⟨hl, hu⟩
    exact abs_le.mpr ⟨by linarith only [hl, hδ1], by linarith only [hu, hδ1]⟩
  have ha2 : |a ^ 2| ≤ 4 := by rw [abs_pow]; nlinarith only [ha, abs_nonneg a]
  have hasq : |a ^ 2 - 1| ≤ 3 * δ := by
    rw [show a ^ 2 - 1 = (a - 1) * (a + 1) by ring, abs_mul]
    have hap : |a + 1| ≤ 3 := by
      have h := abs_add_le a 1
      norm_num at h
      linarith only [ha, h]
    have h := mul_le_mul ha1 hap (abs_nonneg _) hδ.le
    simpa only [mul_comm] using h
  have hb : |b| ≤ δ := (hlabel x).2.2.le
  have hCη := mul_le_mul_of_nonneg_right hC hη.le
  have heps0 : 2 * η < eps := by nlinarith only [hηeq, hCη, hη]
  have heps1 : (4 + C) * η < eps := by nlinarith only [hηeq, hCη, hη]
  have heps2 : (10 + 4 * C) * η < eps := by nlinarith only [hηeq, hCη, hη]
  refine ⟨herr0.trans heps0, ?_, ?_⟩
  · rw [(hqd x).deriv]
    have heq : a • deriv r (ψ x) - deriv c x =
        a • (deriv r (ψ x) - deriv c x) + (a - 1) • deriv c x := by module
    change ‖a • deriv r (ψ x) - deriv c x‖ < eps
    rw [heq]
    apply lt_of_le_of_lt (norm_add_le _ _)
    have ht1 : ‖a • (deriv r (ψ x) - deriv c x)‖ ≤ 4 * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul ha herr1.le (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
      nlinarith only [h]
    have ht2 : ‖(a - 1) • deriv c x‖ ≤ C * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul (ha1.trans hδη) (hcb1 x) (norm_nonneg _) hη.le
      simpa only [mul_comm] using h
    exact (add_le_add ht1 ht2).trans_lt (by nlinarith only [heps1])
  · rw [hqdd x]
    have heq : a ^ 2 • deriv (deriv r) (ψ x) + b • deriv r (ψ x) -
        deriv (deriv c) x =
        a ^ 2 • (deriv (deriv r) (ψ x) - deriv (deriv c) x) +
        (a ^ 2 - 1) • deriv (deriv c) x +
        b • (deriv r (ψ x) - deriv c x) + b • deriv c x := by module
    change ‖a ^ 2 • deriv (deriv r) (ψ x) + b • deriv r (ψ x) -
      deriv (deriv c) x‖ < eps
    rw [heq]
    have ht1 : ‖a ^ 2 • (deriv (deriv r) (ψ x) - deriv (deriv c) x)‖ ≤ 8 * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul ha2 herr2.le (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith only [h]
    have ht2 : ‖(a ^ 2 - 1) • deriv (deriv c) x‖ ≤ 3 * C * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul (hasq.trans (mul_le_mul_of_nonneg_left hδη (by norm_num)))
        (hcb2 x) (norm_nonneg _) (show 0 ≤ 3 * η by positivity)
      nlinarith only [h]
    have ht3 : ‖b • (deriv r (ψ x) - deriv c x)‖ ≤ 2 * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul (hb.trans hδ1) herr1.le (norm_nonneg _) zero_le_one
      simpa only [one_mul] using h
    have ht4 : ‖b • deriv c x‖ ≤ C * η := by
      rw [norm_smul, Real.norm_eq_abs]
      have h := mul_le_mul (hb.trans hδη) (hcb1 x) (norm_nonneg _) hη.le
      simpa only [mul_comm] using h
    have hsum := (norm_add_le
      (a ^ 2 • (deriv (deriv r) (ψ x) - deriv (deriv c) x) +
        (a ^ 2 - 1) • deriv (deriv c) x + b • (deriv r (ψ x) - deriv c x))
      (b • deriv c x)).trans (add_le_add
        ((norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)) le_rfl)
    exact hsum.trans_lt (by nlinarith only [ht1, ht2, ht3, ht4, heps2])

end PoincareConjecture.M63
