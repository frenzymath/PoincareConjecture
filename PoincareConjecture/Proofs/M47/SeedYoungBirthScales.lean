import PoincareConjecture.Proofs.M47.FirstFailureWindow
import PoincareConjecture.Proofs.M47.SeedObservedScaledDensity

set_option autoImplicit false

open Set

universe u

namespace PoincareConjecture.Proofs.M47

theorem exists_seed_young_birth_scale
    {A alpha B lambda : ℝ} (hA : 1 ≤ A) (halpha : 0 < alpha)
    (hB : 1 ≤ B) (hlambda : 0 < lambda) :
    ∃ M : ℝ, 0 < M ∧ 1 ≤ M ∧ 2 * B ≤ M ∧
      ∀ d rNext : ℝ, 0 < d → 0 < rNext → d ≤ rNext ^ 2 / (32 * A) →
        let H := M / d
        let r := lambda / Real.sqrt H
        0 < H ∧ rNext⁻¹ ^ 2 ≤ H ∧ 0 < r ∧
          r ≤ (Real.sqrt (alpha * d) / (4 * A)) / 2 ∧
          4 * B / d ≤ 2 * H ∧
          r = lambda * Real.sqrt d / Real.sqrt M := by
  let M := max (2 * B) (max 1 (64 * A ^ 2 * lambda ^ 2 / alpha))
  have hMone : 1 ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hM : 0 < M := (by linarith only [hB] : 0 < 2 * B).trans_le (le_max_left _ _)
  have hMB : 2 * B ≤ M := le_max_left _ _
  have hMscale : 64 * A ^ 2 * lambda ^ 2 ≤ alpha * M := by
    have h := (div_le_iff₀ halpha).mp
      ((le_max_right _ _).trans (le_max_right _ _) :
        64 * A ^ 2 * lambda ^ 2 / alpha ≤ M)
    nlinarith only [h]
  have hApos : 0 < A := zero_lt_one.trans_le hA
  refine ⟨M, hM, hMone, hMB, ?_⟩
  intro d rNext hd hrNext hyoung
  dsimp only
  have hH : 0 < M / d := div_pos hM hd
  have hrootM : 0 < Real.sqrt M := Real.sqrt_pos.mpr hM
  have hrootd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have hr : 0 < lambda / Real.sqrt (M / d) := div_pos hlambda (Real.sqrt_pos.mpr hH)
  have hdscale : d ≤ rNext ^ 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 32 * A)).mp hyoung
    nlinarith only [h, hA, hd]
  have hlevel : rNext⁻¹ ^ 2 ≤ M / d := by
    calc
      rNext⁻¹ ^ 2 = 1 / (rNext ^ 2) := by rw [inv_pow, inv_eq_one_div]
      _ ≤ 1 / d := one_div_le_one_div_of_le hd hdscale
      _ ≤ M / d := div_le_div_of_nonneg_right hMone hd.le
  have heq : lambda / Real.sqrt (M / d) = lambda * Real.sqrt d / Real.sqrt M := by
    rw [Real.sqrt_div hM.le]
    field_simp
  have hcoefficient : 8 * A * lambda ≤ Real.sqrt alpha * Real.sqrt M := by
    apply (sq_le_sq₀ (by positivity) (by positivity)).mp
    simp only [mul_pow, Real.sq_sqrt halpha.le, Real.sq_sqrt hM.le]
    nlinarith only [hMscale]
  have hradius : lambda / Real.sqrt (M / d) ≤
      (Real.sqrt (alpha * d) / (4 * A)) / 2 := by
    rw [heq, Real.sqrt_mul halpha.le]
    have hid : Real.sqrt alpha * Real.sqrt d / (4 * A) / 2 =
        Real.sqrt alpha * Real.sqrt d / (8 * A) := by ring
    rw [hid]
    apply (div_le_div_iff₀ hrootM (by positivity : 0 < 8 * A)).mpr
    have h := mul_le_mul_of_nonneg_right hcoefficient hrootd.le
    nlinarith only [h]
  have hscalar : 4 * B / d ≤ 2 * (M / d) := by
    calc
      4 * B / d = 2 * (2 * B / d) := by ring
      _ ≤ 2 * (M / d) := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right hMB hd.le) (by norm_num)
  exact ⟨hH, hlevel, hr, hradius, hscalar, heq⟩

theorem seed_young_birth_search_window
    {K : MetricSurgeryConstants} (p : SurgeryParameterPrefix K)
    {F : SurgeryFlowData.{u}} {O : SurgeryObservation F}
    {rNext T d a : ℝ} (hrNext : 0 < rNext)
    (hrLast : rNext ≤ p.r (Fin.last p.i))
    (hT : T ∈ Ico (surgeryEpochStart p.i) O.H)
    (hd : 0 ≤ d) (hyoung : d ≤ rNext ^ 2 / 32)
    (ha : a ≤ rNext ^ 2 / 624) :
    Icc (T - d - a) (T - d) ⊆
      surgeryObservationInterval O ∩ Ici (surgeryEpochStart (p.i - 1)) := by
  have hbottom := firstFailure_neck_bottom_after_overlap p hrNext hrLast hT.1
    (le_rfl (a := rNext⁻¹ ^ 2))
  simp only [← inv_pow, inv_inv] at hbottom
  have hsum : d + a ≤ rNext ^ 2 := by
    nlinarith only [hyoung, ha, sq_nonneg rNext]
  have hprevious : 0 ≤ surgeryEpochStart (p.i - 1) := by
    unfold surgeryEpochStart
    positivity
  intro s hs
  have hlower : surgeryEpochStart (p.i - 1) ≤ s := by
    linarith only [hs.1, hsum, hbottom]
  exact ⟨⟨hprevious.trans hlower, by linarith only [hs.2, hd, hT.2]⟩, hlower⟩

end PoincareConjecture.Proofs.M47
